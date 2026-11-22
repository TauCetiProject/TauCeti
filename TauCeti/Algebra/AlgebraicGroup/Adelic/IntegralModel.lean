/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Adelic.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Smooth
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Integral models of affine groups and their local and global integral points

An `S`-integral model `IntegralModel R K H S` of `G = Spec H` packages a finitely presented
commutative Hopf algebra `coordinate` over `S.integer K` with
`baseChangeEquiv : K ⊗[S.integer K] coordinate ≃ₐc[K] H`. Via `pointsContinuousMulEquiv` and
`subringPoints`, a model `M` defines:
* open closed (compact for finite residue fields) subgroups `M.localPoints v hv ≤ G(K_v)` for
  `v ∉ S`, and `M.level v`;
* `T`-integral subgroups `M.globalPoints T hST ≤ G(K)`, scalar enlargement `M.enlarge hSS'`, and
  eventual model independence `level_eventuallyEq`;
* concrete models `trivial`, `additive`, and `scaledAdditive`, witnessing via
  `exists_scaledAdditive_coordinate_eq_and_localPoints_lt` that `localPoints` depends on
  `baseChangeEquiv` and not on `coordinate` alone (Conrad 2012, Remark 3.5).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3, Thm. 3.4, and Rem. 3.5, pp. 4–6.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open Filter IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped TensorProduct

namespace TauCeti

universe u v uH w w'

/-- An `S`-integral model of `Spec H` over `S.integer K`: a finitely presented commutative Hopf
algebra `coordinate` over `S.integer K` together with a generic-fibre bialgebra equivalence with
`H`. -/
structure IntegralModel (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type uH) [CommRing H] [HopfAlgebra K H] (S : Set (HeightOneSpectrum R)) where
  /-- The integral coordinate commutative Hopf algebra over `S.integer K`. -/
  coordinate : _root_.CommHopfAlgCat.{w'} (S.integer K)
  /-- Finite presentation of the integral coordinate algebra over `S.integer K`. -/
  [finitePresentation : Algebra.FinitePresentation (S.integer K) coordinate]
  /-- Identification of the generic fibre `K ⊗[S.integer K] coordinate` with `H`. -/
  baseChangeEquiv : K ⊗[S.integer K] coordinate ≃ₐc[K] H

attribute [instance] IntegralModel.finitePresentation

namespace IntegralModel

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type uH} [CommRing H] [HopfAlgebra K H] {S : Set (HeightOneSpectrum R)}

/-- Because `S.integer K` is Noetherian, any finite-type commutative Hopf algebra over
`S.integer K` with generic fibre `H` defines an `IntegralModel`. -/
def ofFiniteType (C : _root_.CommHopfAlgCat.{w'} (S.integer K))
    [Algebra.FiniteType (S.integer K) C] (e : K ⊗[S.integer K] C ≃ₐc[K] H) :
    IntegralModel R K H S :=
  letI : Algebra.FinitePresentation (S.integer K) C :=
    (Algebra.FinitePresentation.of_finiteType (R := S.integer K) (A := C)).mp inferInstance
  { coordinate := C, baseChangeEquiv := e }

/-- An `R`-model `C₀` of `H` induces an `S`-integral model for every `S` by scalar extension. -/
noncomputable def ofBaseRing (S : Set (HeightOneSpectrum R)) (C₀ : _root_.CommHopfAlgCat.{w'} R)
    [Algebra.FiniteType R C₀] (e : K ⊗[R] C₀ ≃ₐc[K] H) : IntegralModel R K H S :=
  letI := Algebra.FiniteType.baseChange (R := R) (A := C₀) (S.integer K)
  ofFiniteType (CommHopfAlgCat.baseChange (K := S.integer K) C₀)
    ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R (S.integer K) C₀ K).trans e)

/-- The generic-fibre coordinate algebra `H` of `M` is finitely presented over `K`. -/
theorem finitePresentation_genericFiber (M : IntegralModel R K H S) :
    Algebra.FinitePresentation K H :=
  letI := Algebra.FinitePresentation.baseChange (R := S.integer K) (A := M.coordinate) K
  Algebra.FinitePresentation.equiv M.baseChangeEquiv.toAlgEquiv

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is of finite type over `K`. -/
theorem finiteType_genericFiber (M : IntegralModel R K H S) : Algebra.FiniteType K H :=
  have := M.finitePresentation_genericFiber; inferInstance

/-- Canonical ring homomorphism `m ↦ M.baseChangeEquiv (1 ⊗ₜ m)` into `H`. -/
noncomputable def embed (M : IntegralModel R K H S) : M.coordinate →+* H :=
  M.baseChangeEquiv.toAlgEquiv.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := S.integer K) (A := K) (B := M.coordinate)).toRingHom

/-- `M.embed` sends `m : M.coordinate` to `M.baseChangeEquiv (1 ⊗ₜ m)`. -/
theorem embed_apply (M : IntegralModel R K H S) (m : M.coordinate) :
    M.embed m = M.baseChangeEquiv (1 ⊗ₜ[S.integer K] m) := (rfl)

/-- On pure tensors `c ⊗ₜ m`, `M.baseChangeEquiv` acts as `c • M.embed m`. -/
theorem baseChangeEquiv_tmul (M : IntegralModel R K H S) (c : K) (m : M.coordinate) :
    M.baseChangeEquiv (c ⊗ₜ[S.integer K] m) = c • M.embed m := by
  simpa [TensorProduct.smul_tmul', embed_apply] using map_smul M.baseChangeEquiv c (1 ⊗ₜ m)

/-- `M.embed` sends scalars from `S.integer K` to their images under `algebraMap K H`. -/
@[simp]
theorem embed_algebraMap (M : IntegralModel R K H S) (x : S.integer K) :
    M.embed (algebraMap (S.integer K) M.coordinate x) = algebraMap K H (x : K) := by
  rw [embed_apply, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
    smul_eq_mul, mul_one, M.baseChangeEquiv_tmul, map_one, Algebra.smul_def, mul_one]

/-- Canonical group isomorphism identifying `A`-valued `(S.integer K)`-points of `M.coordinate`
with `A`-valued `K`-points of `H`, for any commutative `K`-algebra `A`. -/
noncomputable def pointsMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
    (BialgEquiv.mapDomainMulEquiv (A := A) M.baseChangeEquiv).symm

/-- Restricting a `K`-point `g` along `(M.pointsMulEquiv A).symm` evaluates `g` on `M.embed`. -/
@[simp]
theorem pointsMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (g : WithConv (H →ₐ[K] A)) (m : M.coordinate) :
    ((M.pointsMulEquiv A).symm g).ofConv m = g.ofConv (M.embed m) := by
  simp [pointsMulEquiv, embed_apply]

/-- Evaluating `M.pointsMulEquiv A x` at `M.embed m` recovers `x.ofConv m`. -/
@[simp]
theorem pointsMulEquiv_apply_ofConv_embed (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) (m : M.coordinate) :
    (M.pointsMulEquiv A x).ofConv (M.embed m) = x.ofConv m := by
  simpa using (M.pointsMulEquiv_symm_apply_ofConv (M.pointsMulEquiv A x) m).symm

/-- Evaluating `M.pointsMulEquiv A x` on `M.baseChangeEquiv (c ⊗ₜ m)` gives `c • x.ofConv m`. -/
theorem pointsMulEquiv_apply_ofConv_baseChangeEquiv (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) (c : K) (m : M.coordinate) :
    (M.pointsMulEquiv A x).ofConv (M.baseChangeEquiv (c ⊗ₜ[S.integer K] m)) = c • x.ofConv m := by
  rw [M.baseChangeEquiv_tmul, map_smul, M.pointsMulEquiv_apply_ofConv_embed]

@[instance_reducible]
private noncomputable def subringAlgebra {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Algebra (S.integer K) B :=
  ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra

private noncomputable def subringInclusion {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    letI := subringAlgebra B hB; B →ₐ[S.integer K] A :=
  letI := subringAlgebra B hB; { B.subtype with commutes' := fun _ ↦ rfl }

/-- Subgroup of `WithConv (H →ₐ[K] A)` of points arising from `B`-valued `(S.integer K)`-points of
`M.coordinate`, for a subring `B : Subring A` containing the image of `S.integer K`. -/
noncomputable def subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Subgroup (WithConv (H →ₐ[K] A)) :=
  letI := subringAlgebra B hB
  ((M.pointsMulEquiv A).toMonoidHom.comp
    (AlgHom.mapValue (H := M.coordinate) (subringInclusion B hB))).range

/-- `g ∈ M.subringPoints B hB` iff `g` sends every integral coordinate `M.embed m` into `B`. -/
@[simp]
theorem mem_subringPoints_iff (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ B := by
  let := subringAlgebra B hB
  rw [subringPoints, MonoidHom.range_comp, Subgroup.mem_map_equiv, MonoidHom.mem_range,
    ← MonoidHom.mem_mrange, AlgHom.mem_mrange_mapValue_iff B.subtype_injective]
  refine forall_congr' fun m ↦ ?_
  have hrange : ((subringInclusion B hB).range : Set A) = (B : Set A) := Subtype.range_coe
  rw [M.pointsMulEquiv_symm_apply_ofConv, ← SetLike.mem_coe, hrange, SetLike.mem_coe]

/-- Membership in `M.subringPoints B hB` reduces to an `(S.integer K)`-algebra generating family. -/
theorem mem_subringPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {ι : Type*} {a : ι → M.coordinate} (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ i, g.ofConv (M.embed (a i)) ∈ B := by
  let := subringAlgebra B hB
  rw [subringPoints, MonoidHom.range_comp, Subgroup.mem_map_equiv, MonoidHom.mem_range]
  have hmem : (∃ x, AlgHom.mapValue (subringInclusion B hB) x = (M.pointsMulEquiv A).symm g) ↔
      ((M.pointsMulEquiv A).symm g).ofConv ∈ Set.range
        ((subringInclusion B hB).comp : (M.coordinate →ₐ[S.integer K] B) → _) :=
    ⟨fun ⟨x, hx⟩ ↦ ⟨x.ofConv, by simp [← hx]⟩,
     fun ⟨x, hx⟩ ↦ ⟨toConv x, WithConv.ofConv_injective (by simp [hx])⟩⟩
  simp only [hmem, AlgHom.range_comp_left_eq_of_adjoin_eq_top (subringInclusion B hB)
    B.subtype_injective ha, Set.mem_ofPred_eq, pointsMulEquiv_symm_apply_ofConv]
  exact forall_congr' fun _ ↦ ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

/-- Canonical topological group isomorphism identifying `A`-valued `(S.integer K)`-points of
`M.coordinate` with `A`-valued `K`-points of `H` for a commutative topological `K`-algebra `A`. -/
noncomputable def pointsContinuousMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃ₜ* WithConv (H →ₐ[K] A) where
  toMulEquiv := M.pointsMulEquiv A
  continuous_toFun := ((BialgHom.continuous_mapDomain M.baseChangeEquiv.symm.toBialgHom).comp
    (AlgHom.continuous_baseChangePointsMulEquiv (k := S.integer K) (K := K))).congr
    fun _ ↦ by simp [pointsMulEquiv]
  continuous_invFun := continuous_withConv_iff.2 fun m ↦ by
    simpa only [MulEquiv.invFun_eq_symm, M.pointsMulEquiv_symm_apply_ofConv] using
      continuous_eval_ofConv (M.embed m)

/-- The underlying `MulEquiv` of `M.pointsContinuousMulEquiv A` is `M.pointsMulEquiv A`. -/
@[simp]
theorem coe_pointsContinuousMulEquiv (M : IntegralModel R K H S) (A : Type w) [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    (M.pointsContinuousMulEquiv A :
      WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A)) =
      M.pointsMulEquiv A := (rfl)

/-- The forward map of `M.pointsContinuousMulEquiv A` is `M.pointsMulEquiv A`. -/
@[simp]
theorem pointsContinuousMulEquiv_apply (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A]
    (x : WithConv (M.coordinate →ₐ[S.integer K] A)) :
    M.pointsContinuousMulEquiv A x = M.pointsMulEquiv A x := (rfl)

/-- The inverse map of `M.pointsContinuousMulEquiv A` is `(M.pointsMulEquiv A).symm`. -/
@[simp]
theorem pointsContinuousMulEquiv_symm_apply (M : IntegralModel R K H S) {A : Type w} [CommRing A]
    [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] (g : WithConv (H →ₐ[K] A)) :
    (M.pointsContinuousMulEquiv A).symm g = (M.pointsMulEquiv A).symm g := (rfl)

/-- Restricting a `K`-point `g` along `(M.pointsContinuousMulEquiv A).symm` evaluates `g` on
`M.embed`. -/
theorem pointsContinuousMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S) {A : Type w}
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A]
    (g : WithConv (H →ₐ[K] A)) (m : M.coordinate) :
    ((M.pointsContinuousMulEquiv A).symm g).ofConv m = g.ofConv (M.embed m) :=
  M.pointsMulEquiv_symm_apply_ofConv g m

/-- When `B` is open in `A`, `M.subringPoints B hB` is open in `WithConv (H →ₐ[K] A)`. -/
theorem isOpen_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBopen : IsOpen (B : Set A)) :
    IsOpen (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact ((M.pointsContinuousMulEquiv A).toHomeomorph.isOpenEmbedding.comp
    (AlgHom.isOpenEmbedding_mapValue (ψ := subringInclusion B hB)
      hBopen.isOpenEmbedding_subtypeVal)).isOpen_range

/-- When `B` is closed in `A`, `M.subringPoints B hB` is closed in `WithConv (H →ₐ[K] A)`. -/
theorem isClosed_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBclosed : IsClosed (B : Set A)) :
    IsClosed (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact ((M.pointsContinuousMulEquiv A).toHomeomorph.isClosedEmbedding.comp
    (AlgHom.isClosedEmbedding_mapValue (ψ := subringInclusion B hB)
      hBclosed.isClosedEmbedding_subtypeVal)).isClosed_range

/-- When `B` is compact inside a T1 topological ring `A`, `M.subringPoints B hB` is compact. -/
theorem isCompact_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) [CompactSpace B] :
    IsCompact (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact isCompact_range ((M.pointsContinuousMulEquiv A).continuous.comp
    (AlgHom.continuous_mapValue (ψ := subringInclusion B hB) continuous_subtypeVal))

/-- For `v ∉ S`, `M.localPoints v hv` is the subgroup `𝒢(𝒪_v) ≤ G(K_v)` of `v`-integral points. -/
noncomputable def localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    (hv : v ∉ S) : Subgroup (LocalPoints K H v) :=
  M.subringPoints (v.adicCompletionIntegers K).toSubring fun x ↦
    (v.algebraMap_mem_adicCompletionIntegers_iff (x : K)).mpr (x.property v hv)

/-- `g ∈ M.localPoints v hv` iff `g` evaluates every integral coordinate into `𝒪_v`. -/
@[simp]
theorem mem_localPoints_iff (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K H v} :
    g ∈ M.localPoints v hv ↔
      ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ v.adicCompletionIntegers K :=
  M.mem_subringPoints_iff (v.adicCompletionIntegers K).toSubring _

/-- Membership in `M.localPoints v hv` reduces to an `(S.integer K)`-algebra generating family. -/
theorem mem_localPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {v : HeightOneSpectrum R} (hv : v ∉ S) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤) {g : LocalPoints K H v} :
    g ∈ M.localPoints v hv ↔ ∀ i, g.ofConv (M.embed (a i)) ∈ v.adicCompletionIntegers K :=
  M.mem_subringPoints_iff_of_adjoin_eq_top (v.adicCompletionIntegers K).toSubring _ ha

/-- `M.localPoints v hv` is an open subgroup of `LocalPoints K H v`. -/
theorem isOpen_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsOpen (M.localPoints v hv : Set (LocalPoints K H v)) :=
  M.isOpen_subringPoints (v.adicCompletionIntegers K).toSubring _ (Valued.isOpen_valuationSubring _)

/-- `M.localPoints v hv` is closed in `LocalPoints K H v`. -/
theorem isClosed_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsClosed (M.localPoints v hv : Set (LocalPoints K H v)) :=
  Subgroup.isClosed_of_isOpen (M.localPoints v hv) (M.isOpen_localPoints v hv)

/-- When `R ⧸ v.asIdeal` is finite, `M.localPoints v hv` is compact. -/
theorem isCompact_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] (hv : v ∉ S) :
    IsCompact (M.localPoints v hv : Set (LocalPoints K H v)) := by
  have hset : ((v.adicCompletionIntegers K).toSubring : Set (v.adicCompletion K)) =
      Set.range ((↑) : v.adicCompletionIntegers K → v.adicCompletion K) := by
    ext x; simp [ValuationSubring.mem_toSubring]
  let _ : CompactSpace (v.adicCompletionIntegers K).toSubring :=
    isCompact_iff_compactSpace.mp (hset ▸ isCompact_range continuous_subtypeVal)
  exact M.isCompact_subringPoints (v.adicCompletionIntegers K).toSubring _

open scoped Classical in
/-- Reference subgroup family across finite places: `M.localPoints v hv` outside `S`, `⊤` on `S`. -/
noncomputable def level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    Subgroup (LocalPoints K H v) := if hv : v ∈ S then ⊤ else M.localPoints v hv

/-- At `v ∈ S`, `M.level v = ⊤`. -/
@[simp]
theorem level_of_mem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∈ S) :
    M.level v = ⊤ := by simp [level, hv]

/-- At `v ∉ S`, `M.level v = M.localPoints v hv`. -/
@[simp]
theorem level_of_notMem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    M.level v = M.localPoints v hv := by simp [level, hv]

/-- Every reference subgroup `M.level v` is open in `LocalPoints K H v`. -/
theorem isOpen_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsOpen (M.level v : Set (LocalPoints K H v)) := by
  by_cases hv : v ∈ S <;> simp [hv, M.isOpen_localPoints]

/-- Every reference subgroup `M.level v` is closed in `LocalPoints K H v`. -/
theorem isClosed_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsClosed (M.level v : Set (LocalPoints K H v)) :=
  Subgroup.isClosed_of_isOpen (M.level v) (M.isOpen_level v)

/-- `M.level v` bundled as an `OpenSubgroup` of `LocalPoints K H v`. -/
noncomputable def openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    OpenSubgroup (LocalPoints K H v) := ⟨M.level v, M.isOpen_level v⟩

/-- The underlying `Subgroup` of `M.openLevel v` is `M.level v`. -/
@[simp]
theorem coe_openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    (M.openLevel v : Subgroup (LocalPoints K H v)) = M.level v := (rfl)

/-- Membership in `M.openLevel v` agrees with membership in `M.level v`. -/
@[simp]
theorem mem_openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    {g : LocalPoints K H v} : g ∈ M.openLevel v ↔ g ∈ M.level v := Iff.rfl

/-- For `S = ∅` and finite residue fields, `M.localPoints` packages as `CompactOpenSubgroups`. -/
noncomputable def compactOpenSubgroups (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    CompactOpenSubgroups (LocalPoints (R := R) K H) where
  subgroup v := M.openLevel v
  isCompact_subgroup v := by
    rw [← OpenSubgroup.coe_toSubgroup, M.coe_openLevel, M.level_of_notMem (Set.notMem_empty v)]
    exact M.isCompact_localPoints v (Set.notMem_empty v)

/-- At `v`, `M.compactOpenSubgroups.subgroup v` is `M.openLevel v`. -/
@[simp]
theorem compactOpenSubgroups_subgroup (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] (v : HeightOneSpectrum R) :
    M.compactOpenSubgroups.subgroup v = M.openLevel v := (rfl)

/-- For `T ⊇ S`, `M.globalPoints T hST` is the subgroup `𝒢(𝒪_{K,T}) ≤ G(K)` of `T`-integral
`K`-rational points. -/
noncomputable def globalPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : Subgroup (WithConv (H →ₐ[K] K)) :=
  M.subringPoints (T.integer K).toSubring fun x ↦ Set.integer_mono K hST x.property

/-- `g ∈ M.globalPoints T hST` iff its values on `M.embed` lie in `T.integer K`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ T.integer K :=
  M.mem_subringPoints_iff (T.integer K).toSubring _

/-- Enlarging `T` enlarges `M.globalPoints`. -/
theorem globalPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.globalPoints T₁ hST₁ ≤ M.globalPoints T₂ (hST₁.trans hT₁₂) := fun _ hg ↦
  (mem_globalPoints_iff M _).mpr fun m ↦
    Set.integer_mono K hT₁₂ ((mem_globalPoints_iff M _).mp hg m)

/-- Local-global characterization: `g ∈ M.globalPoints T hST` iff `LocalPoints.diagonal K H v g ∈
M.localPoints v` for all `v ∉ T`. -/
theorem mem_globalPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
      LocalPoints.diagonal K H v g ∈ M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_globalPoints_iff, Set.mem_integer_iff, mem_localPoints_iff,
    LocalPoints.diagonal_apply_ofConv, HeightOneSpectrum.algebraMap_mem_adicCompletionIntegers_iff]
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

section Enlarge

variable {S' : Set (HeightOneSpectrum R)}

/-- Scalar extension along `S.integer K → S'.integer K` (`S ⊆ S'`) produces an `S'`-integral model
whose generic-fibre identification factors through `baseChangeTowerBialgEquiv`. -/
noncomputable def enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S') : IntegralModel R K H S' :=
  letI := integerInclusionAlgebra K hSS'; haveI := isScalarTower_integerInclusionAlgebra K hSS'
  letI := Algebra.FinitePresentation.baseChange (R := S.integer K) (A := M.coordinate)
    (S'.integer K)
  { coordinate := CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate
    baseChangeEquiv := (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
      (S.integer K) (S'.integer K) M.coordinate K).trans M.baseChangeEquiv }

/-- Canonical `S'.integer K`-algebra equivalence identifying `(M.enlarge hSS').coordinate` with
`S'.integer K ⊗[S.integer K] M.coordinate` (`M.coordinate.baseChangeAlgEquiv`). -/
noncomputable def enlargeCoordinateEquiv (M : IntegralModel R K H S) (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra K hSS'
    (M.enlarge hSS').coordinate ≃ₐ[S'.integer K] S'.integer K ⊗[S.integer K] M.coordinate :=
  letI := integerInclusionAlgebra K hSS'; M.coordinate.baseChangeAlgEquiv (K := S'.integer K)

/-- Under `enlargeCoordinateEquiv`, `(M.enlarge hSS').embed` sends a pure tensor `c ⊗ₜ m` to
`(c : K) • M.embed m`. -/
@[simp]
theorem embed_enlargeCoordinateEquiv_symm_tmul (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (c : S'.integer K) (m : M.coordinate) :
    letI := integerInclusionAlgebra K hSS'
    (M.enlarge hSS').embed ((M.enlargeCoordinateEquiv hSS').symm (c ⊗ₜ[S.integer K] m)) =
      (c : K) • M.embed m := by
  let := integerInclusionAlgebra K hSS'; have := isScalarTower_integerInclusionAlgebra K hSS'
  refine ((M.enlarge hSS').embed_apply _).trans <| (congrArg (M.enlarge hSS').baseChangeEquiv <|
    congrArg (1 ⊗ₜ[S'.integer K] ·) (M.coordinate.baseChangeAlgEquiv_symm_apply _)).trans ?_
  change M.baseChangeEquiv (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv (S.integer K)
    (S'.integer K) M.coordinate K (1 ⊗ₜ[S'.integer K] (c ⊗ₜ[S.integer K] m))) = _
  rw [Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul, Subalgebra.smul_def,
    smul_eq_mul, mul_one, M.baseChangeEquiv_tmul]

/-- Enlarging `S` to `S'` preserves `subringPoints` for subrings containing `S'.integer K`. -/
theorem subringPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB' : ∀ y : S'.integer K, algebraMap K A (y : K) ∈ B) :
    (M.enlarge hSS').subringPoints B hB' =
      M.subringPoints B (fun x ↦ hB' ⟨x.val, Set.integer_mono K hSS' x.property⟩) := by
  let := integerInclusionAlgebra K hSS'
  ext g; simp only [mem_subringPoints_iff]
  refine ⟨fun h m ↦ ?_, fun h t ↦ ?_⟩
  · simpa only [M.embed_enlargeCoordinateEquiv_symm_tmul hSS', Subalgebra.coe_one, one_smul] using
      h ((M.enlargeCoordinateEquiv hSS').symm ((1 : S'.integer K) ⊗ₜ[S.integer K] m))
  · rw [← (M.enlargeCoordinateEquiv hSS').symm_apply_apply t]
    exact TensorProduct.inductionOn (M.enlargeCoordinateEquiv hSS' t)
      (fun c m ↦ by rw [M.embed_enlargeCoordinateEquiv_symm_tmul hSS', map_smul,
        Algebra.smul_def]; exact B.mul_mem (hB' c) (h m))
      fun _ _ hx hy ↦ by rw [map_add, map_add, map_add]; exact B.add_mem hx hy

/-- Enlarging `S` to `S'` leaves `localPoints` unchanged at every place `v ∉ S'`. -/
@[simp]
theorem localPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (v : HeightOneSpectrum R) (hv : v ∉ S') :
    (M.enlarge hSS').localPoints v hv = M.localPoints v (fun hvS ↦ hv (hSS' hvS)) :=
  M.subringPoints_enlarge hSS' (v.adicCompletionIntegers K).toSubring _

/-- Enlarging `S` to `S'` leaves `level v` unchanged at every place `v ∉ S'`. -/
theorem level_enlarge_of_notMem (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {v : HeightOneSpectrum R} (hv : v ∉ S') : (M.enlarge hSS').level v = M.level v := by
  rw [(M.enlarge hSS').level_of_notMem hv, M.level_of_notMem (fun hvS ↦ hv (hSS' hvS)),
    M.localPoints_enlarge hSS' v hv]

/-- Enlarging `S` to `S'` leaves `globalPoints T` unchanged for every `T ⊇ S'`. -/
@[simp]
theorem globalPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').globalPoints T hS'T = M.globalPoints T (hSS'.trans hS'T) :=
  M.subringPoints_enlarge hSS' (T.integer K).toSubring _

end Enlarge

/-- For every fixed `h : H`, at all but finitely many places `v`, if `v ∉ S` then every
`g ∈ M.localPoints v hv` evaluates `h` into `v.adicCompletionIntegers K`. -/
theorem eventually_localPoints_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (h : H) :
    ∀ᶠ v in cofinite, ∀ (hv : v ∉ S), ∀ g ∈ M.localPoints v hv,
      g.ofConv h ∈ v.adicCompletionIntegers K := by
  suffices ∀ t : K ⊗[S.integer K] M.coordinate, ∀ᶠ v in cofinite, ∀ (hv : v ∉ S),
      ∀ g ∈ M.localPoints v hv, g.ofConv (M.baseChangeEquiv t) ∈ v.adicCompletionIntegers K by
    simpa only [M.baseChangeEquiv.apply_symm_apply] using this (M.baseChangeEquiv.symm h)
  intro t; refine TensorProduct.inductionOn t (fun c m ↦ ?_) (fun _ _ hx hy ↦ ?_)
  · filter_upwards [(algebraMap K (FiniteAdeleRing R K) c).property] with v hc hv g hg
    rw [M.baseChangeEquiv_tmul, map_smul, Algebra.smul_def]
    exact mul_mem hc ((M.mem_localPoints_iff hv).mp hg m)
  · filter_upwards [hx, hy] with v hvx hvy hv g hg
    rw [map_add, map_add]; exact add_mem (hvx hv g hg) (hvy hv g hg)

/-- When `S` is finite, for every `h : H`, eventually every `g ∈ M.level v` maps `h` into `𝒪_v`. -/
theorem eventually_level_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (hS : S.Finite) (h : H) :
    ∀ᶠ v in cofinite, ∀ g ∈ M.level v, g.ofConv h ∈ v.adicCompletionIntegers K := by
  filter_upwards [hS.compl_mem_cofinite, M.eventually_localPoints_ofConv_mem h] with v hv hloc g hg
  rw [M.level_of_notMem hv] at hg; exact hloc hv g hg

/-- If `S₁` is finite, then `M₁.level v ≤ M₂.level v` at all but finitely many places `v`. -/
theorem level_eventuallyLE {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂) (hS₁ : S₁.Finite) :
    ∀ᶠ v in cofinite, M₁.level v ≤ M₂.level v := by
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := S₂.integer K) (A := M₂.coordinate)
  have hgen : Algebra.adjoin (S₂.integer K) (Set.range ((↑) : F → M₂.coordinate)) = ⊤ := by
    simpa using hF
  filter_upwards [eventually_all.mpr fun i : F ↦
    M₁.eventually_level_ofConv_mem hS₁ (M₂.embed i)] with v hv g hg
  by_cases hv₂ : v ∈ S₂
  · rw [M₂.level_of_mem hv₂]; exact Subgroup.mem_top g
  · rw [M₂.level_of_notMem hv₂, M₂.mem_localPoints_iff_of_adjoin_eq_top hv₂ hgen]
    exact fun i ↦ hv i g hg

/-- Independence of the integral model away from finitely many places (Conrad 2012, Prop. 3.3). -/
theorem level_eventuallyEq {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) : ∀ᶠ v in cofinite, M₁.level v = M₂.level v := by
  filter_upwards [level_eventuallyLE M₁ M₂ hS₁, level_eventuallyLE M₂ M₁ hS₂] with _ h₁₂ h₂₁
  exact le_antisymm h₁₂ h₂₁

section ConcreteModels

variable (R K S)

/-- Canonical `S`-integral model of `Spec K`, with coordinate ring `S.integer K`. -/
noncomputable def trivial : IntegralModel R K K S where
  coordinate := _root_.CommHopfAlgCat.of (S.integer K) (S.integer K)
  baseChangeEquiv :=
    BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.rid (S.integer K) K K) (by ext) (by ext)

/-- Standard `S`-integral model of `𝔾ₐ = Spec (SymmetricAlgebra K K)` over `S.integer K`. -/
@[expose] noncomputable def additive : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv := AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)

/-- `c`-scaled `S`-integral model of `𝔾ₐ`: same integral `coordinate` as `additive`, with
`baseChangeEquiv` scaling the additive generator by `c : Kˣ`. -/
@[expose] noncomputable def scaledAdditive (c : Kˣ) :
    IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv :=
    (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)).trans
      (BialgEquiv.ofAlgEquiv (SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c))
        (by apply SymmetricAlgebra.algHom_ext; ext; simp [SymmetricAlgebra.counitAlgHom_eq,
              SymmetricAlgebra.map_apply_ι, Units.smul_def, SymmetricAlgebra.algebraMapInv_ι])
        (by apply SymmetricAlgebra.algHom_ext; ext; simp [SymmetricAlgebra.comul_ι,
              SymmetricAlgebra.map_apply_ι, Units.smul_def]))

variable {R K S}

/-- `(scaledAdditive R K S c).coordinate` is literally `(additive R K S).coordinate`. -/
@[simp]
theorem scaledAdditive_coordinate (c : Kˣ) :
    (scaledAdditive R K S c).coordinate = (additive R K S).coordinate := (rfl)

/-- `(additive R K S).embed` sends `SymmetricAlgebra.ι _ _ r` to
`SymmetricAlgebra.ι K K (r : K)`. -/
@[simp]
theorem additive_embed_ι (r : S.integer K) :
    (additive R K S).embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) r) =
      SymmetricAlgebra.ι K K (r : K) :=
  ((additive R K S).embed_apply _).trans <|
    (AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι (K := K) 1 r).trans (by simp)

/-- `(scaledAdditive R K S c).embed` sends `SymmetricAlgebra.ι _ _ r` to
`SymmetricAlgebra.ι K K ((c : K) * (r : K))`. -/
@[simp]
theorem scaledAdditive_embed_ι (c : Kˣ) (r : S.integer K) :
    (scaledAdditive R K S c).embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) r) =
      SymmetricAlgebra.ι K K ((c : K) * (r : K)) := by
  refine ((scaledAdditive R K S c).embed_apply _).trans ?_
  change SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c)
    (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)
      (1 ⊗ₜ[S.integer K] SymmetricAlgebra.ι (S.integer K) (S.integer K) r)) = _
  simp [Units.smul_def]

private theorem adjoin_gaGenerator_eq_top :
    Algebra.adjoin (S.integer K) (Set.range fun _ : Unit ↦
      (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1 :
        AdditiveGroup.coordinateHopfAlgebra (S.integer K))) = ⊤ :=
  SymmetricAlgebra.adjoin_range_ι_comp_eq_top_of_span_eq_top _
    (by rw [Set.range_const]; exact Ideal.span_singleton_one)

/-- At `v ∉ S`, `g ∈ (scaledAdditive R K S c).localPoints v hv` iff `c * (gaPointsMulEquiv g).toAdd`
lies in `v.adicCompletionIntegers K`. -/
theorem mem_localPoints_scaledAdditive_iff (c : Kˣ) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K (SymmetricAlgebra K K) v} :
    g ∈ (scaledAdditive R K S c).localPoints v hv ↔
      algebraMap K (v.adicCompletion K) (c : K) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  rw [(scaledAdditive R K S c).mem_localPoints_iff_of_adjoin_eq_top hv adjoin_gaGenerator_eq_top,
    Unique.forall_iff, scaledAdditive_embed_ι, Subalgebra.coe_one, mul_one,
    SymmetricAlgebra.ι_self_eq_smul_ι_one, map_smul, Algebra.smul_def,
    AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- At `v ∉ S`, `g ∈ (additive R K S).localPoints v hv` iff its additive parameter lies in `𝒪_v`. -/
theorem mem_localPoints_additive_iff {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K (SymmetricAlgebra K K) v} :
    g ∈ (additive R K S).localPoints v hv ↔
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  rw [(additive R K S).mem_localPoints_iff_of_adjoin_eq_top hv adjoin_gaGenerator_eq_top,
    Unique.forall_iff, additive_embed_ι, Subalgebra.coe_one, AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- Local integral subgroups depend on `baseChangeEquiv`, not on `coordinate` alone
(Conrad 2012, Remark 3.5). -/
theorem exists_scaledAdditive_coordinate_eq_and_localPoints_lt {v : HeightOneSpectrum R}
    (hv : v ∉ S) :
    ∃ c : Kˣ, (scaledAdditive R K S c).coordinate = (additive R K S).coordinate ∧
      (additive R K S).localPoints v hv < (scaledAdditive R K S c).localPoints v hv := by
  obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let c : Kˣ := Units.mk0 (algebraMap R K r)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0)
  have hval : v.valuation K (c : K) < 1 := (v.valuation_lt_one_iff_mem r).mpr hrv
  refine ⟨c, rfl, lt_of_le_not_ge (fun g hg ↦ (mem_localPoints_scaledAdditive_iff c hv).mpr
    (mul_mem ((v.algebraMap_mem_adicCompletionIntegers_iff _).mpr hval.le)
      ((mem_localPoints_additive_iff hv).mp hg))) fun hle ↦ ?_⟩
  have hg_std : (AdditiveGroup.gaPointsMulEquiv (R := K) (A := v.adicCompletion K)).symm
      (Multiplicative.ofAdd (algebraMap K (v.adicCompletion K) (c : K)⁻¹)) ∈
      (additive R K S).localPoints v hv := hle <| by simp [mem_localPoints_scaledAdditive_iff c hv]
  simp only [mem_localPoints_additive_iff hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    HeightOneSpectrum.algebraMap_mem_adicCompletionIntegers_iff] at hg_std
  exact not_lt_of_ge hg_std (((v.valuation K).val_lt_one_iff c.ne_zero).mp hval)

end ConcreteModels

end IntegralModel

end TauCeti
