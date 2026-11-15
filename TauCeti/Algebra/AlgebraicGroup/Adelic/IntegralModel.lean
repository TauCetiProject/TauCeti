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

Let `R` be a Dedekind domain with fraction field `K`, `H` a commutative Hopf `K`-algebra
representing `G = Spec H`, and `S : Set (HeightOneSpectrum R)` a set of finite places. An
*integral model* `IntegralModel R K H S` packages a finitely presented commutative Hopf algebra
`coordinate` over `S.integer K` with `baseChangeEquiv : K ⊗[S.integer K] coordinate ≃ₐc[K] H`.

Through a unified `subringPoints` construction for subrings `B ≤ A` containing the image of
`S.integer K`, a model `M` defines:
* open closed (and, for finite residue fields, compact) subgroups `M.localPoints v hv ≤ G(K_v)` for
  `v ∉ S`, extended by `⊤` on `S` to the reference family `M.level v`;
* `T`-integral rational subgroups `M.globalPoints T hST ≤ G(K)` characterized locally for `v ∉ T`;
* scalar enlargement `M.enlarge hSS'` and eventual model independence `level_eventuallyEq`;
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
noncomputable def ofBaseRing (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{w'} R) [Algebra.FiniteType R C₀]
    (e : K ⊗[R] C₀ ≃ₐc[K] H) : IntegralModel R K H S :=
  letI : Algebra.FiniteType (S.integer K) (CommHopfAlgCat.baseChange (K := S.integer K) C₀) :=
    Algebra.FiniteType.baseChange (S.integer K)
  ofFiniteType (CommHopfAlgCat.baseChange (K := S.integer K) C₀)
    ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R (S.integer K) C₀ K).trans e)

/-- The generic-fibre coordinate algebra `H` of `M` is finitely presented over `K`. -/
theorem finitePresentation_genericFiber (M : IntegralModel R K H S) :
    Algebra.FinitePresentation K H :=
  letI : Algebra.FinitePresentation K (K ⊗[S.integer K] M.coordinate) :=
    Algebra.FinitePresentation.baseChange K
  Algebra.FinitePresentation.equiv M.baseChangeEquiv.toAlgEquiv

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is of finite type over `K`. -/
theorem finiteType_genericFiber (M : IntegralModel R K H S) : Algebra.FiniteType K H := by
  have := M.finitePresentation_genericFiber; infer_instance

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
  have hcm : (c ⊗ₜ[S.integer K] m : K ⊗[S.integer K] M.coordinate) =
      c • ((1 : K) ⊗ₜ[S.integer K] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hcm, map_smul, embed_apply]

/-- `M.embed` sends scalars from `S.integer K` to their images under `algebraMap K H`. -/
@[simp]
theorem embed_algebraMap (M : IntegralModel R K H S) (x : S.integer K) :
    M.embed (algebraMap (S.integer K) M.coordinate x) = algebraMap K H (x : K) := by
  have htmul : ((1 : K) ⊗ₜ[S.integer K] algebraMap (S.integer K) M.coordinate x) =
      ((x : K) ⊗ₜ[S.integer K] (1 : M.coordinate)) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
      smul_eq_mul, mul_one]
  rw [embed_apply, htmul, M.baseChangeEquiv_tmul, map_one, Algebra.smul_def, mul_one]

private noncomputable def coordinatePointsMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
    (BialgEquiv.mapDomainMulEquiv (A := A) M.baseChangeEquiv).symm

private theorem coordinatePointsMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (g : WithConv (H →ₐ[K] A)) (m : M.coordinate) :
    ((M.coordinatePointsMulEquiv A).symm g).ofConv m = g.ofConv (M.embed m) := by
  simp [coordinatePointsMulEquiv, embed_apply]

@[instance_reducible]
private noncomputable def subringAlgebra {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Algebra (S.integer K) B :=
  ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra

private noncomputable def subringInclusion {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    letI := subringAlgebra B hB
    B →ₐ[S.integer K] A :=
  letI := subringAlgebra B hB
  { B.subtype with commutes' := fun _ ↦ rfl }

/-- Subgroup of `WithConv (H →ₐ[K] A)` of points arising from `B`-valued `(S.integer K)`-points of
`M.coordinate`, for a subring `B : Subring A` containing the image of `S.integer K`. -/
noncomputable def subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Subgroup (WithConv (H →ₐ[K] A)) :=
  letI := subringAlgebra B hB
  ((M.coordinatePointsMulEquiv A).toMonoidHom.comp
    (AlgHom.mapValue (H := M.coordinate) (subringInclusion B hB))).range

/-- `g ∈ M.subringPoints B hB` iff `g` sends every integral coordinate `M.embed m` into `B`. -/
@[simp]
theorem mem_subringPoints_iff (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ B := by
  let := subringAlgebra B hB
  rw [subringPoints, MonoidHom.mem_range]
  have hmem : (∃ x, ((M.coordinatePointsMulEquiv A).toMonoidHom.comp
        (AlgHom.mapValue (H := M.coordinate) (subringInclusion B hB))) x = g) ↔
      (M.coordinatePointsMulEquiv A).symm g ∈
        MonoidHom.mrange (AlgHom.mapValue (H := M.coordinate) (subringInclusion B hB)) :=
    ⟨fun ⟨x, hx⟩ ↦ ⟨x, (M.coordinatePointsMulEquiv A).eq_symm_apply.mpr hx⟩,
      fun ⟨x, hx⟩ ↦ ⟨x, by
        simpa [MonoidHom.comp_apply] using congrArg (M.coordinatePointsMulEquiv A) hx⟩⟩
  rw [hmem, AlgHom.mem_mrange_mapValue_iff B.subtype_injective]
  refine forall_congr' fun m ↦ ?_
  have hrange : ((subringInclusion B hB).range : Set A) = (B : Set A) := Subtype.range_coe
  rw [M.coordinatePointsMulEquiv_symm_apply_ofConv, ← SetLike.mem_coe, hrange, SetLike.mem_coe]

/-- Membership in `M.subringPoints B hB` reduces to an `(S.integer K)`-algebra generating family. -/
theorem mem_subringPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {ι : Type*} {a : ι → M.coordinate} (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ i, g.ofConv (M.embed (a i)) ∈ B := by
  rw [mem_subringPoints_iff]
  refine ⟨fun h i ↦ h (a i), fun h m ↦ ?_⟩
  have hm : m ∈ Algebra.adjoin (S.integer K) (Set.range a) := ha ▸ Algebra.mem_top
  exact Algebra.adjoin_induction (fun _ ⟨i, hi⟩ ↦ hi ▸ h i)
    (fun x ↦ by rw [M.embed_algebraMap, AlgHom.commutes]; exact hB x)
    (fun _ _ _ _ hx hy ↦ by rw [map_add, map_add]; exact B.add_mem hx hy)
    (fun _ _ _ _ hx hy ↦ by rw [map_mul, map_mul]; exact B.mul_mem hx hy) hm

private noncomputable def coordinatePointsContinuousMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃ₜ* WithConv (H →ₐ[K] A) where
  toMulEquiv := M.coordinatePointsMulEquiv A
  continuous_toFun := by
    let hbc : Continuous (AlgHom.baseChangePointsMulEquiv
        (k := S.integer K) (K := K) (A := M.coordinate) (R := A)) :=
      isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
        ((baseChangeHomeomorph (S.integer K) K M.coordinate A).symm.continuous.comp
          isHomeomorph_ofConv.continuous).congr fun x ↦
            Algebra.TensorProduct.ext (by ext) <| AlgHom.ext fun m ↦ by
              simp only [Function.comp_apply]
              exact (baseChangeHomeomorph_symm_apply_tmul (k := S.integer K) (K := K)
                x.ofConv 1 m).trans (AlgHom.baseChangePointsMulEquiv_apply_tmul
                  (k := S.integer K) (K := K) (A := M.coordinate) (R := A) x 1 m).symm
    exact ((BialgHom.continuous_mapDomain M.baseChangeEquiv.symm.toBialgHom).comp hbc).congr
      fun _ ↦ by simp [coordinatePointsMulEquiv]
  continuous_invFun := continuous_withConv_iff.2 fun m ↦ by
    simpa only [MulEquiv.invFun_eq_symm, M.coordinatePointsMulEquiv_symm_apply_ofConv] using
      continuous_eval_ofConv (M.embed m)

/-- When `B` is open in `A`, `M.subringPoints B hB` is open in `WithConv (H →ₐ[K] A)`. -/
theorem isOpen_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBopen : IsOpen (B : Set A)) :
    IsOpen (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isOpenEmbedding.comp
    (AlgHom.isOpenEmbedding_mapValue (H₁ := M.coordinate)
      (ψ := subringInclusion B hB) hBopen.isOpenEmbedding_subtypeVal)).isOpen_range

/-- When `B` is closed in `A`, `M.subringPoints B hB` is closed in `WithConv (H →ₐ[K] A)`. -/
theorem isClosed_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBclosed : IsClosed (B : Set A)) :
    IsClosed (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isClosedEmbedding.comp
    (AlgHom.isClosedEmbedding_mapValue (H₁ := M.coordinate)
      (ψ := subringInclusion B hB) hBclosed.isClosedEmbedding_subtypeVal)).isClosed_range

/-- When `B` is compact inside a T1 topological ring `A`, `M.subringPoints B hB` is compact. -/
theorem isCompact_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) [CompactSpace B] :
    IsCompact (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let := subringAlgebra B hB
  exact isCompact_range ((M.coordinatePointsContinuousMulEquiv A).continuous.comp
    (AlgHom.continuous_mapValue (H₁ := M.coordinate)
      (ψ := subringInclusion B hB) continuous_subtype_val))

/-- For `v ∉ S`, `M.localPoints v hv` is the subgroup `𝒢(𝒪_v) ≤ G(K_v)` of `v`-integral points. -/
noncomputable def localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    (hv : v ∉ S) : Subgroup (LocalPoints K H v) :=
  M.subringPoints (v.adicCompletionIntegers K).toSubring fun x ↦
    (v.algebraMap_mem_adicCompletionIntegers_iff (x : K)).mpr (x.2 v hv)

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
  let _ : CompactSpace (v.adicCompletionIntegers K).toSubring :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  exact M.isCompact_subringPoints (v.adicCompletionIntegers K).toSubring _

open scoped Classical in
/-- Reference subgroup family across finite places: `M.localPoints v hv` outside `S`, `⊤` on `S`. -/
noncomputable def level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    Subgroup (LocalPoints K H v) :=
  if hv : v ∈ S then ⊤ else M.localPoints v hv

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
  by_cases hv : v ∈ S
  · rw [M.level_of_mem hv]; exact isOpen_univ
  · rw [M.level_of_notMem hv]; exact M.isOpen_localPoints v hv

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
  M.subringPoints (T.integer K).toSubring fun x v hv ↦ x.2 v fun hvS ↦ hv (hST hvS)

/-- `g ∈ M.globalPoints T hST` iff its values on `M.embed` lie in `T.integer K`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ T.integer K :=
  M.mem_subringPoints_iff (T.integer K).toSubring _

/-- Enlarging `T` enlarges `M.globalPoints`. -/
theorem globalPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.globalPoints T₁ hST₁ ≤ M.globalPoints T₂ (hST₁.trans hT₁₂) := fun _ hg ↦ by
  rw [mem_globalPoints_iff] at hg ⊢; exact fun m v hv ↦ hg m v fun hv₁ ↦ hv (hT₁₂ hv₁)

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

@[instance_reducible]
private noncomputable def integerInclusionAlgebra (hSS' : S ⊆ S') :
    Algebra (S.integer K) (S'.integer K) :=
  (Subalgebra.inclusion (S := S.integer K) (T := S'.integer K)
    (fun _ hx v hv ↦ hx v fun hvS ↦ hv (hSS' hvS))).toRingHom.toAlgebra

private theorem integerInclusionScalarTower (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra (K := K) hSS'
    IsScalarTower (S.integer K) (S'.integer K) K :=
  let := integerInclusionAlgebra (K := K) hSS'
  IsScalarTower.of_algebraMap_eq' rfl

/-- Scalar extension along `S.integer K → S'.integer K` (`S ⊆ S'`) produces an `S'`-integral model
whose generic-fibre identification factors through `baseChangeTowerBialgEquiv`. -/
noncomputable def enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S') : IntegralModel R K H S' :=
  letI := integerInclusionAlgebra (K := K) hSS'
  haveI := integerInclusionScalarTower (K := K) hSS'
  letI : Algebra.FinitePresentation (S'.integer K)
      (CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate) :=
    Algebra.FinitePresentation.baseChange (S'.integer K)
  { coordinate := CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate
    baseChangeEquiv :=
      (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
        (S.integer K) (S'.integer K) M.coordinate K).trans M.baseChangeEquiv }

private noncomputable def enlargeCoordinateEquiv (M : IntegralModel R K H S) (hSS' : S ⊆ S') :
    letI := integerInclusionAlgebra (K := K) hSS'
    (S'.integer K ⊗[S.integer K] M.coordinate) ≃+* (M.enlarge hSS').coordinate :=
  letI := integerInclusionAlgebra (K := K) hSS'
  RingEquiv.refl _

private theorem embed_enlarge_tmul (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (c : S'.integer K) (m : M.coordinate) :
    letI := integerInclusionAlgebra (K := K) hSS'
    (M.enlarge hSS').embed (M.enlargeCoordinateEquiv hSS' (c ⊗ₜ[S.integer K] m)) =
      (c : K) • M.embed m := by
  let := integerInclusionAlgebra (K := K) hSS'
  have := integerInclusionScalarTower (K := K) hSS'
  rw [embed_apply]
  exact (BialgEquiv.trans_apply
    (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv
      (S.integer K) (S'.integer K) M.coordinate K)
    M.baseChangeEquiv (1 ⊗ₜ[S'.integer K] (c ⊗ₜ[S.integer K] m))).trans <|
    (congrArg M.baseChangeEquiv
      (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul
        (S.integer K) (S'.integer K) M.coordinate K 1 c m)).trans <| by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_one, M.baseChangeEquiv_tmul]

/-- Enlarging `S` to `S'` preserves `subringPoints` for subrings containing `S'.integer K`. -/
theorem subringPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB' : ∀ y : S'.integer K, algebraMap K A (y : K) ∈ B) :
    (M.enlarge hSS').subringPoints B hB' =
      M.subringPoints B (fun x ↦ hB' ⟨x.1, fun v hv ↦ x.2 v fun hvS ↦ hv (hSS' hvS)⟩) := by
  let := integerInclusionAlgebra (K := K) hSS'
  obtain ⟨e, he⟩ : ∃ e : (S'.integer K ⊗[S.integer K] M.coordinate) ≃+*
      (M.enlarge hSS').coordinate,
      ∀ (c : S'.integer K) (m : M.coordinate),
        (M.enlarge hSS').embed (e (c ⊗ₜ[S.integer K] m)) = (c : K) • M.embed m :=
    ⟨M.enlargeCoordinateEquiv hSS', M.embed_enlarge_tmul hSS'⟩
  ext g
  simp only [mem_subringPoints_iff]
  refine ⟨fun h m ↦ ?_, fun h t ↦ ?_⟩
  · simpa only [he 1 m, Subalgebra.coe_one, one_smul] using
      h (e ((1 : S'.integer K) ⊗ₜ[S.integer K] m))
  · rw [← e.apply_symm_apply t]
    exact TensorProduct.inductionOn (e.symm t)
      (fun c m ↦ by
        rw [he c m, map_smul, Algebra.smul_def]
        exact B.mul_mem (hB' c) (h m))
      (fun _ _ hx hy ↦ by
        rw [map_add, map_add, map_add]
        exact B.add_mem hx hy)

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
  · filter_upwards [(algebraMap K (FiniteAdeleRing R K) c).2] with v hc hv g hg
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
noncomputable def additive : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv := AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)

private noncomputable def scaleGaBialgEquiv {K : Type v} [Field K] (c : Kˣ) :
    SymmetricAlgebra K K ≃ₐc[K] SymmetricAlgebra K K :=
  BialgEquiv.ofAlgEquiv (SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c))
    (by apply SymmetricAlgebra.algHom_ext; ext
        simp [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.map_apply_ι,
          Units.smul_def, SymmetricAlgebra.algebraMapInv_ι])
    (by apply SymmetricAlgebra.algHom_ext; ext
        simp [SymmetricAlgebra.comul_ι, SymmetricAlgebra.map_apply_ι, Units.smul_def])

/-- `c`-scaled `S`-integral model of `𝔾ₐ`: same integral `coordinate` as `additive`, with
`baseChangeEquiv` scaling the additive generator by `c : Kˣ`. -/
noncomputable def scaledAdditive (c : Kˣ) : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv :=
    (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)).trans
      (scaleGaBialgEquiv c)

variable {R K S}

/-- `(scaledAdditive R K S c).coordinate` is literally `(additive R K S).coordinate`. -/
@[simp]
theorem scaledAdditive_coordinate (c : Kˣ) :
    (scaledAdditive R K S c).coordinate = (additive R K S).coordinate := (rfl)

private theorem adjoin_gaGenerator_eq_top :
    Algebra.adjoin (S.integer K)
      (Set.range fun _ : Unit ↦
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
  have hembed : (scaledAdditive R K S c).embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) =
      SymmetricAlgebra.ι K K (c : K) :=
    ((scaledAdditive R K S c).embed_apply _).trans <|
      (BialgEquiv.trans_apply
        (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K))
        (scaleGaBialgEquiv c) _).trans <|
      (congrArg (scaleGaBialgEquiv c)
        (AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι (k := S.integer K) (K := K) 1 1)).trans
      (by simp [scaleGaBialgEquiv, BialgEquiv.ofAlgEquiv_apply, Units.smul_def])
  rw [(scaledAdditive R K S c).mem_localPoints_iff_of_adjoin_eq_top hv adjoin_gaGenerator_eq_top,
    Unique.forall_iff, hembed]
  have hc : SymmetricAlgebra.ι K K (c : K) = (c : K) • SymmetricAlgebra.ι K K 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hc, map_smul, Algebra.smul_def, AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- At `v ∉ S`, `g ∈ (additive R K S).localPoints v hv` iff its additive parameter lies in `𝒪_v`. -/
theorem mem_localPoints_additive_iff {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K (SymmetricAlgebra K K) v} :
    g ∈ (additive R K S).localPoints v hv ↔
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  have hembed : (additive R K S).embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) =
      SymmetricAlgebra.ι K K 1 :=
    ((additive R K S).embed_apply _).trans <|
      (AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι (k := S.integer K) (K := K) 1 1).trans
      (by simp)
  rw [(additive R K S).mem_localPoints_iff_of_adjoin_eq_top hv adjoin_gaGenerator_eq_top,
    Unique.forall_iff, hembed, AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- Local integral subgroups depend on `baseChangeEquiv`, not on `coordinate` alone
(Conrad 2012, Remark 3.5). -/
theorem exists_scaledAdditive_coordinate_eq_and_localPoints_lt {v : HeightOneSpectrum R}
    (hv : v ∉ S) :
    ∃ c : Kˣ, (scaledAdditive R K S c).coordinate = (additive R K S).coordinate ∧
      (additive R K S).localPoints v hv < (scaledAdditive R K S c).localPoints v hv := by
  obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc0 : algebraMap R K r ≠ 0 := fun h ↦
    hr0 (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  let c : Kˣ := Units.mk0 (algebraMap R K r) hc0
  have hval_lt : Valued.v (algebraMap K (v.adicCompletion K) (c : K)) < 1 := by
    rw [v.valued_algebraMap_adicCompletion, Units.val_mk0, v.valuation_of_algebraMap,
      v.intValuation_lt_one_iff_mem]
    exact hrv
  have hc_mem : algebraMap K (v.adicCompletion K) (c : K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hval_lt.le
  refine ⟨c, rfl, lt_of_le_not_ge (fun g hg ↦ ?_) (fun hle ↦ ?_)⟩
  · rw [mem_localPoints_additive_iff hv] at hg
    exact (mem_localPoints_scaledAdditive_iff c hv).mpr (mul_mem hc_mem hg)
  · let g : LocalPoints K (SymmetricAlgebra K K) v :=
      (AdditiveGroup.gaPointsMulEquiv (R := K) (A := v.adicCompletion K)).symm
        (Multiplicative.ofAdd (algebraMap K (v.adicCompletion K) ((c⁻¹ : Kˣ) : K)))
    have hg_std : g ∈ (additive R K S).localPoints v hv := hle <| by
      rw [mem_localPoints_scaledAdditive_iff c hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
        ← map_mul, Units.mul_inv, map_one]
      exact one_mem _
    rw [mem_localPoints_additive_iff hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
      map_inv₀] at hg_std
    have hne : Valued.v (algebraMap K (v.adicCompletion K) (c : K)) ≠ 0 :=
      (Valued.v).ne_zero_iff.mpr ((algebraMap K (v.adicCompletion K)).injective.ne hc0)
    have hmul := mul_le_mul_of_nonneg_left hg_std
      (zero_le (a := Valued.v (algebraMap K (v.adicCompletion K) (c : K))))
    rw [mul_inv_cancel₀ hne, mul_one] at hmul
    exact not_lt_of_ge hmul hval_lt

end ConcreteModels

end IntegralModel

end TauCeti
