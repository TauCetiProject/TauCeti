/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
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
`coordinate` over `S.integer K` together with `baseChangeIso : K ⊗[S.integer K] coordinate ≅ H`.

Through a unified `subringPoints` construction for subrings `B ≤ A` containing the image of
`S.integer K`, a model `M` defines:
* open closed (and, for finite residue fields, compact) subgroups `M.localPoints v hv ≤ G(K_v)` for
  `v ∉ S`, extended by `⊤` on `S` to the reference family `M.level v`;
* `T`-integral rational subgroups `M.globalPoints T hST ≤ G(K)` characterized locally for `v ∉ T`;
* scalar enlargement `M.enlarge hSS'` and eventual model independence `level_eventuallyEq`;
* concrete models `trivial`, `additive`, and `scaledAdditive`, witnessing via
  `exists_scaledAdditive_coordinate_eq_and_localPoints_lt` that `localPoints` depends on
  `baseChangeIso` and not on `coordinate` alone (Conrad 2012, Remark 3.5).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3, Thm. 3.4, and Rem. 3.5, pp. 4–6.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open CategoryTheory Filter IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped TensorProduct

namespace TauCeti

universe u v w

/-- An `S`-integral model of `Spec H` over `S.integer K`: a finitely presented commutative Hopf
algebra `coordinate` over `S.integer K` together with a generic-fibre isomorphism with `H`. -/
structure IntegralModel (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type v) [CommRing H] [HopfAlgebra K H] (S : Set (HeightOneSpectrum R)) where
  /-- The integral coordinate commutative Hopf algebra over `S.integer K`. -/
  coordinate : _root_.CommHopfAlgCat.{v} (S.integer K)
  /-- Finite presentation of the integral coordinate algebra over `S.integer K`. -/
  [finitePresentation : Algebra.FinitePresentation (S.integer K) coordinate]
  /-- Identification of the generic fibre `K ⊗[S.integer K] coordinate` with `H`. -/
  baseChangeIso : CommHopfAlgCat.baseChange (K := K) coordinate ≅ _root_.CommHopfAlgCat.of K H

attribute [instance] IntegralModel.finitePresentation

namespace IntegralModel

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H] {S : Set (HeightOneSpectrum R)}

/-- Because `S.integer K` is Noetherian, any finite-type commutative Hopf algebra over
`S.integer K` with generic fibre `H` defines an `IntegralModel`. -/
def ofFiniteType (C : _root_.CommHopfAlgCat.{v} (S.integer K))
    [Algebra.FiniteType (S.integer K) C]
    (e : CommHopfAlgCat.baseChange (K := K) C ≅ _root_.CommHopfAlgCat.of K H) :
    IntegralModel R K H S :=
  letI : Algebra.FinitePresentation (S.integer K) C :=
    (Algebra.FinitePresentation.of_finiteType (R := S.integer K) (A := C)).mp inferInstance
  { coordinate := C, baseChangeIso := e }

/-- An `R`-model `C₀` of `H` induces an `S`-integral model for every `S` by scalar extension. -/
noncomputable def ofBaseRing (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{v} R) [Algebra.FiniteType R C₀]
    (e : CommHopfAlgCat.baseChange (K := K) C₀ ≅ _root_.CommHopfAlgCat.of K H) :
    IntegralModel R K H S :=
  letI : Algebra.FiniteType (S.integer K) (CommHopfAlgCat.baseChange (K := S.integer K) C₀) :=
    Algebra.FiniteType.baseChange (S.integer K)
  ofFiniteType (CommHopfAlgCat.baseChange (K := S.integer K) C₀)
    (CommHopfAlgCat.baseChangeTowerIso R K C₀ ≪≫ e)

/-- The generic-fibre coordinate algebra `H` of `M` is finitely presented over `K`. -/
theorem finitePresentation_genericFiber (M : IntegralModel R K H S) :
    Algebra.FinitePresentation K H :=
  letI : Algebra.FinitePresentation K (K ⊗[S.integer K] M.coordinate) :=
    Algebra.FinitePresentation.baseChange K
  Algebra.FinitePresentation.equiv (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).toAlgEquiv

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is of finite type over `K`. -/
theorem finiteType_genericFiber (M : IntegralModel R K H S) : Algebra.FiniteType K H := by
  have := M.finitePresentation_genericFiber; infer_instance

/-- Canonical ring homomorphism `m ↦ M.baseChangeIso.hom.hom (1 ⊗ₜ m)` into `H`. -/
noncomputable def embed (M : IntegralModel R K H S) : M.coordinate →+* H :=
  M.baseChangeIso.hom.hom.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := S.integer K) (A := K) (B := M.coordinate)).toRingHom

/-- `M.embed` sends `m : M.coordinate` to `M.baseChangeIso.hom.hom (1 ⊗ₜ m)`. -/
@[simp]
theorem embed_apply (M : IntegralModel R K H S) (m : M.coordinate) :
    M.embed m = M.baseChangeIso.hom.hom (1 ⊗ₜ[S.integer K] m) := (rfl)

/-- On pure tensors `c ⊗ₜ m`, `M.baseChangeIso.hom.hom` acts as `c • M.embed m`. -/
theorem baseChangeIso_hom_tmul (M : IntegralModel R K H S) (c : K) (m : M.coordinate) :
    M.baseChangeIso.hom.hom (c ⊗ₜ[S.integer K] m) = c • M.embed m := by
  have hcm : (c ⊗ₜ[S.integer K] m : K ⊗[S.integer K] M.coordinate) =
      c • ((1 : K) ⊗ₜ[S.integer K] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hcm, map_smul, embed_apply]

private noncomputable def coordinatePointsMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
    (BialgEquiv.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm)

/-- Subgroup of `WithConv (H →ₐ[K] A)` of points arising from `B`-valued `(S.integer K)`-points of
`M.coordinate`, for a subring `B : Subring A` containing the image of `S.integer K`. -/
noncomputable def subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Subgroup (WithConv (H →ₐ[K] A)) :=
  letI : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  ((M.coordinatePointsMulEquiv A).toMonoidHom.comp (AlgHom.mapValue (H := M.coordinate) ιB)).range

/-- `g ∈ M.subringPoints B hB` iff `g` sends every integral coordinate `M.embed m` into `B`. -/
@[simp]
theorem mem_subringPoints_iff (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ B := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  have hmem : g ∈ M.subringPoints B hB ↔ (M.coordinatePointsMulEquiv A).symm g ∈
      MonoidHom.mrange (AlgHom.mapValue (H := M.coordinate) ιB) := by
    delta subringPoints
    -- Rebind the unfolded `let` to `ιB` before rewriting range membership via `eq_symm_apply`.
    change g ∈ ((M.coordinatePointsMulEquiv A).toMonoidHom.comp
      (AlgHom.mapValue (H := M.coordinate) ιB)).range ↔ _
    rw [MonoidHom.mem_range, MonoidHom.mem_mrange]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, (M.coordinatePointsMulEquiv A).eq_symm_apply.mpr hx⟩,
      fun ⟨x, hx⟩ ↦ ⟨x, by
        simpa [MonoidHom.comp_apply] using congrArg (M.coordinatePointsMulEquiv A) hx⟩⟩
  rw [hmem, AlgHom.mem_mrange_mapValue_iff B.subtype_injective]
  refine forall_congr' fun m ↦ ?_
  have heval : ((M.coordinatePointsMulEquiv A).symm g).ofConv m = g.ofConv (M.embed m) := by
    simp [coordinatePointsMulEquiv, embed_apply]; rfl
  have hrange : (ιB.range : Set A) = (B : Set A) := Subtype.range_coe
  rw [heval, ← SetLike.mem_coe, hrange, SetLike.mem_coe]

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
  refine Algebra.adjoin_induction (fun _ ⟨i, hi⟩ ↦ hi ▸ h i) (fun x ↦ ?_)
    (fun _ _ _ _ hx hy ↦ by rw [map_add, map_add]; exact B.add_mem hx hy)
    (fun _ _ _ _ hx hy ↦ by rw [map_mul, map_mul]; exact B.mul_mem hx hy) hm
  have htmul : ((1 : K) ⊗ₜ[S.integer K] algebraMap (S.integer K) M.coordinate x) =
      ((x : K) ⊗ₜ[S.integer K] (1 : M.coordinate)) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
      smul_eq_mul, mul_one]
  rw [embed_apply, htmul, M.baseChangeIso_hom_tmul, map_smul, map_one, map_one, Algebra.smul_def,
    mul_one]
  exact hB x

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
    exact ((BialgHom.continuous_mapDomain
      (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm.toBialgHom).comp hbc).congr fun x ↦ by
        simp [coordinatePointsMulEquiv, BialgEquiv.mapDomainMulEquiv_apply,
          BialgHom.mapDomain_apply]
  continuous_invFun := continuous_withConv_iff.2 fun m ↦ by
    have heval (g : WithConv (H →ₐ[K] A)) :
        (((M.coordinatePointsMulEquiv A).symm g).ofConv m) = g.ofConv (M.embed m) := by
      simp [coordinatePointsMulEquiv, embed_apply]; rfl
    simpa only [MulEquiv.invFun_eq_symm, heval] using continuous_eval_ofConv (M.embed m)

/-- When `B` is open in `A`, `M.subringPoints B hB` is open in `WithConv (H →ₐ[K] A)`. -/
theorem isOpen_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBopen : IsOpen (B : Set A)) :
    IsOpen (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  have hι : IsOpenEmbedding ιB := hBopen.isOpenEmbedding_subtypeVal
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isOpenEmbedding.comp
    (AlgHom.isOpenEmbedding_mapValue (H₁ := M.coordinate) hι)).isOpen_range

/-- When `B` is closed in `A`, `M.subringPoints B hB` is closed in `WithConv (H →ₐ[K] A)`. -/
theorem isClosed_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBclosed : IsClosed (B : Set A)) :
    IsClosed (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  have hι : IsClosedEmbedding ιB := hBclosed.isClosedEmbedding_subtypeVal
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isClosedEmbedding.comp
    (AlgHom.isClosedEmbedding_mapValue (H₁ := M.coordinate) hι)).isClosed_range

/-- When `B` is compact inside a T1 topological ring `A`, `M.subringPoints B hB` is compact. -/
theorem isCompact_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) [CompactSpace B] :
    IsCompact (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  exact isCompact_range ((M.coordinatePointsContinuousMulEquiv A).continuous.comp
    (AlgHom.continuous_mapValue (H₁ := M.coordinate)
      (ψ := ({ B.subtype with commutes' := fun _ ↦ rfl } : B →ₐ[S.integer K] A))
      continuous_subtype_val))

/-- For `v ∉ S`, `M.localPoints v hv` is the subgroup `𝒢(𝒪_v) ≤ G(K_v)` of `v`-integral points. -/
noncomputable def localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    (hv : v ∉ S) : Subgroup (LocalPoints K H v) :=
  M.subringPoints (v.adicCompletionIntegers K).toSubring fun x ↦ by
    rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact x.2 v hv

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
    M.level v = ⊤ := by delta level; simp [hv]

/-- At `v ∉ S`, `M.level v = M.localPoints v hv`. -/
@[simp]
theorem level_of_notMem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    M.level v = M.localPoints v hv := by delta level; simp [hv]

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

/-- For `S = ∅` and finite residue fields, `M.localPoints` packages as `CompactOpenSubgroups`. -/
noncomputable def compactOpenSubgroups (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    CompactOpenSubgroups (LocalPoints (R := R) K H) where
  subgroup v := M.openLevel v
  isCompact_subgroup v := by
    -- Unfold the carrier of `M.openLevel v` to `M.level v` so `level_of_notMem` applies.
    change IsCompact (M.level v : Set (LocalPoints K H v))
    rw [M.level_of_notMem (Set.notMem_empty v)]
    exact M.isCompact_localPoints v (Set.notMem_empty v)

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
    LocalPoints.diagonal_apply_ofConv, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

section Enlarge

variable {S' : Set (HeightOneSpectrum R)}

/-- Scalar extension along `S.integer K → S'.integer K` (`S ⊆ S'`) produces an `S'`-integral model
whose generic-fibre identification factors through `baseChangeTowerIso`. -/
noncomputable def enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S') : IntegralModel R K H S' :=
  letI : Algebra (S.integer K) (S'.integer K) :=
    (Subalgebra.inclusion (S := S.integer K) (T := S'.integer K)
      (fun _ hx v hv ↦ hx v fun hvS ↦ hv (hSS' hvS))).toRingHom.toAlgebra
  letI : IsScalarTower (S.integer K) (S'.integer K) K := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FinitePresentation (S'.integer K)
      (CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate) :=
    Algebra.FinitePresentation.baseChange (S'.integer K)
  { coordinate := CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate
    baseChangeIso :=
      CommHopfAlgCat.baseChangeTowerIso (S.integer K) K M.coordinate ≪≫ M.baseChangeIso }

/-- Enlarging `S` to `S'` preserves `subringPoints` for subrings containing `S'.integer K`. -/
theorem subringPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB' : ∀ y : S'.integer K, algebraMap K A (y : K) ∈ B) :
    (M.enlarge hSS').subringPoints B hB' =
      M.subringPoints B (fun x ↦ hB' ⟨x.1, fun v hv ↦ x.2 v fun hvS ↦ hv (hSS' hvS)⟩) := by
  let : Algebra (S.integer K) (S'.integer K) :=
    (Subalgebra.inclusion (S := S.integer K) (T := S'.integer K)
      (fun _ hx v hv ↦ hx v fun hvS ↦ hv (hSS' hvS))).toRingHom.toAlgebra
  have : IsScalarTower (S.integer K) (S'.integer K) K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FinitePresentation (S'.integer K)
      (CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate) :=
    Algebra.FinitePresentation.baseChange (S'.integer K)
  let M' : IntegralModel R K H S' :=
    { coordinate := CommHopfAlgCat.baseChange (K := S'.integer K) M.coordinate
      baseChangeIso :=
        CommHopfAlgCat.baseChangeTowerIso (S.integer K) K M.coordinate ≪≫ M.baseChangeIso }
  have hM' : M.enlarge hSS' = M' := rfl
  have htmul (c : S'.integer K) (m : M.coordinate) :
      M'.embed (c ⊗ₜ[S.integer K] m) = (c : K) • M.embed m := by
    -- Unfold `M'.embed` on the tensor-product carrier so `baseChangeTowerIso_hom_apply` applies.
    change M.baseChangeIso.hom.hom
        ((CommHopfAlgCat.baseChangeTowerIso (S.integer K) K M.coordinate).hom.hom
          ((1 : K) ⊗ₜ[S'.integer K] (c ⊗ₜ[S.integer K] m))) = (c : K) • M.embed m
    rw [CommHopfAlgCat.baseChangeTowerIso_hom_apply, Algebra.smul_def, mul_one]
    exact M.baseChangeIso_hom_tmul (c : K) m
  rw [hM']; ext g; simp only [mem_subringPoints_iff]
  refine ⟨fun h m ↦ by
    simpa only [htmul 1 m, Subalgebra.coe_one, one_smul] using
      h ((1 : S'.integer K) ⊗ₜ[S.integer K] m), fun h t ↦ ?_⟩
  refine TensorProduct.inductionOn t
    (fun c m ↦ by rw [htmul c m, map_smul, Algebra.smul_def]; exact B.mul_mem (hB' c) (h m))
    (fun _ _ hx hy ↦ by rw [map_add, map_add]; exact B.add_mem hx hy)

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
      ∀ g ∈ M.localPoints v hv, g.ofConv (M.baseChangeIso.hom.hom t) ∈ v.adicCompletionIntegers K by
    have ht : M.baseChangeIso.hom.hom (M.baseChangeIso.inv.hom h) = h :=
      (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).apply_symm_apply h
    simpa only [ht] using this (M.baseChangeIso.inv.hom h)
  intro t; refine TensorProduct.inductionOn t (fun c m ↦ ?_) (fun _ _ hx hy ↦ ?_)
  · filter_upwards [(algebraMap K (FiniteAdeleRing R K) c).2] with v hc hv g hg
    rw [M.baseChangeIso_hom_tmul, map_smul, Algebra.smul_def]
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
theorem level_eventuallyLe {S₁ S₂ : Set (HeightOneSpectrum R)}
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
  filter_upwards [level_eventuallyLe M₁ M₂ hS₁, level_eventuallyLe M₂ M₁ hS₂] with _ h₁₂ h₂₁
  exact le_antisymm h₁₂ h₂₁

section ConcreteModels

variable (R K S)

/-- Canonical `S`-integral model of `Spec K`, with coordinate ring `S.integer K`. -/
noncomputable def trivial : IntegralModel R K K S where
  coordinate := _root_.CommHopfAlgCat.of (S.integer K) (S.integer K)
  baseChangeIso := _root_.CommHopfAlgCat.isoMk
    (BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.rid (S.integer K) K K) (by ext) (by ext))

/-- Standard `S`-integral model of `𝔾ₐ = Spec (SymmetricAlgebra K K)` over `S.integer K`. -/
noncomputable def additive : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeIso := AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K

private noncomputable def scaleGaIso {K : Type v} [Field K] (c : Kˣ) :
    AdditiveGroup.coordinateHopfAlgebra K ≅ AdditiveGroup.coordinateHopfAlgebra K :=
  _root_.CommHopfAlgCat.isoMk <|
    BialgEquiv.ofAlgEquiv (SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c))
      (by apply SymmetricAlgebra.algHom_ext; ext
          simp [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.map_apply_ι,
            Units.smul_def, SymmetricAlgebra.algebraMapInv_ι])
      (by apply SymmetricAlgebra.algHom_ext; ext
          simp [SymmetricAlgebra.comul_ι, SymmetricAlgebra.map_apply_ι, Units.smul_def])

/-- `c`-scaled `S`-integral model of `𝔾ₐ`: same integral `coordinate` as `additive`, with
`baseChangeIso` scaling the additive generator by `c : Kˣ`. -/
noncomputable def scaledAdditive (c : Kˣ) : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeIso :=
    AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K ≪≫ scaleGaIso c

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
      SymmetricAlgebra.ι K K (c : K) := by
    -- Unfold `embed` into `gaScalarTensorBialgEquiv` followed by `scaleGaIso`.
    change (scaleGaIso c).hom.hom
        ((AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K))
          ((1 : K) ⊗ₜ[S.integer K] SymmetricAlgebra.ι (S.integer K) (S.integer K) 1)) = _
    rw [AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, map_one, one_smul]
    -- Unfold `scaleGaIso c` on the `SymmetricAlgebra K K` carrier so `mapEquiv_ι` applies.
    change SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c)
      (SymmetricAlgebra.ι K K 1) = _
    rw [SymmetricAlgebra.mapEquiv_ι, DistribMulAction.toLinearEquiv_apply, Units.smul_def,
      smul_eq_mul, mul_one]
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
      SymmetricAlgebra.ι K K 1 := by
    -- Unfold `(additive R K S).embed` to `gaScalarTensorBialgEquiv` on `(1 : K) ⊗ₜ ι 1`.
    change (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K))
      ((1 : K) ⊗ₜ[S.integer K] SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) = _
    rw [AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, map_one, one_smul]
  rw [(additive R K S).mem_localPoints_iff_of_adjoin_eq_top hv adjoin_gaGenerator_eq_top,
    Unique.forall_iff, hembed, AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- Local integral subgroups depend on `baseChangeIso`, not on `coordinate` alone
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
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Units.val_mk0, v.valuation_of_algebraMap, v.intValuation_lt_one_iff_mem]
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
