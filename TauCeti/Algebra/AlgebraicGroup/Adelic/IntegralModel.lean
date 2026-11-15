/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.Adelic.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Smooth
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Integral models of affine groups and their local and global integral points

Let `R` be a Dedekind domain with fraction field `K`, let `H` be a commutative Hopf `K`-algebra
representing an affine group `G = Spec H` over `K`, and let `S : Set (HeightOneSpectrum R)` be a
set of finite places of `R`. An *integral model* of `G` over the ring of `S`-integers `S.integer K`
consists of:

* a finitely presented commutative Hopf algebra `coordinate` over `S.integer K`, and
* an isomorphism `baseChangeIso : K ⊗[S.integer K] coordinate ≅ H` of commutative Hopf
  `K`-algebras identifying its generic fibre with `H`.

Because `S.integer K` is a Dedekind domain and hence Noetherian
(`TauCeti.RingTheory.DedekindDomain.SInteger.Basic`), finite presentation over `S.integer K` is
equivalent to finite type (`IntegralModel.ofFiniteType`), and base-changing to `K` automatically
endows `H` with `Algebra.FinitePresentation K H` (`IntegralModel.finitePresentation_genericFiber`).

From a single model `M : IntegralModel R K H S` we obtain, through a unified `subringPoints`
construction for any `K`-algebra `A` and subring `B ≤ A` containing the image of `S.integer K`:

* at every finite place `v ∉ S`, the subgroup `M.localPoints v hv ≤ LocalPoints K H v` of points
  sending the integral coordinates into `v.adicCompletionIntegers K`, which is open and closed in
  `LocalPoints K H v` and compact whenever the residue field `R ⧸ v.asIdeal` is finite;
* at all finite places `v`, the reference subgroup family `M.level v`, equal to `M.localPoints v hv`
  for `v ∉ S` and `⊤` for `v ∈ S`;
* for any `T ⊇ S`, the `T`-integral rational subgroup `M.globalPoints T hST ≤ WithConv (H →ₐ[K] K)`,
  characterized locally as the `K`-points landing in `M.localPoints v hv` at every `v ∉ T`;
* enlargement `M.enlarge hSS' : IntegralModel R K H S'` along `S ⊆ S'` via `baseChangeTowerIso`,
  preserving `localPoints`, `level` outside `S'`, and `globalPoints`;
* eventual agreement `IntegralModel.level_eventuallyEq`: for any two models `M₁` over finite `S₁`
  and `M₂` over finite `S₂` of the same generic group `H`, `M₁.level v = M₂.level v` for all but
  finitely many finite places `v`.

Finally, `IntegralModel.scaledAdditive` constructs for every `c : Kˣ` an integral model of `𝔾ₐ`
sharing the exact coordinate Hopf algebra of `IntegralModel.additive` whose `baseChangeIso` scales
the additive coordinate by `c`. At any place `v ∉ S`, choosing `c` in `v` yields a strict subgroup
inclusion `(additive R K S).localPoints v hv < (scaledAdditive R K S c).localPoints v hv`
(`exists_scaledAdditive_coordinate_eq_and_localPoints_lt`), demonstrating that `M.localPoints`
genuinely depends on `M.baseChangeIso` and not on `M.coordinate` alone (Conrad 2012, Remark 3.5).

## Main declarations

* `TauCeti.IntegralModel`: bundled `S`-integral model of `Spec H`.
* `TauCeti.IntegralModel.subringPoints`: subgroup of `A`-points of `H` coming from `B`-valued
  points of `M.coordinate`, with openness, closedness, and compactness criteria.
* `TauCeti.IntegralModel.localPoints`, `TauCeti.IntegralModel.level`,
  `TauCeti.IntegralModel.globalPoints`: local, reference-level, and global `T`-integral subgroups.
* `TauCeti.IntegralModel.enlarge`: scalar extension of a model from `S` to `S' ⊇ S`.
* `TauCeti.IntegralModel.level_eventuallyEq`: any two models over finite exceptional sets induce
  eventually equal local subgroup families.
* `TauCeti.IntegralModel.additive`, `TauCeti.IntegralModel.scaledAdditive`,
  `TauCeti.IntegralModel.exists_scaledAdditive_coordinate_eq_and_localPoints_lt`: concrete models
  of `𝔾ₐ` and dependence of `localPoints` on `baseChangeIso`.

## See also

* `TauCeti.Topology.Algebra.PointTopology.IntegralPoints`: openness, closedness, and compactness
  for integral points of a bialgebra defined directly over a valuation ring `𝒪[E]`, which
  `IntegralModel.subringPoints` extends to generic-fibre Hopf algebras equipped with an
  `S.integer K`-model and base-change isomorphism.

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

/-- An `S`-integral model of the affine `K`-group `Spec H` over the ring of `S`-integers
`S.integer K` of a Dedekind domain `R` with fraction field `K`: a finitely presented commutative
Hopf algebra `coordinate` over `S.integer K` together with an isomorphism identifying its base
change to `K` with `H`. -/
structure IntegralModel (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type v) [CommRing H] [HopfAlgebra K H]
    (S : Set (HeightOneSpectrum R)) where
  /-- The integral coordinate commutative Hopf algebra over `S.integer K`. -/
  coordinate : _root_.CommHopfAlgCat.{v} (S.integer K)
  /-- Finite presentation of the integral coordinate algebra over `S.integer K`. -/
  [finitePresentation : Algebra.FinitePresentation (S.integer K) coordinate]
  /-- Identification of the generic fibre `K ⊗[S.integer K] coordinate` with `H`. -/
  baseChangeIso :
    CommHopfAlgCat.baseChange (K := K) coordinate ≅ _root_.CommHopfAlgCat.of K H

attribute [instance] IntegralModel.finitePresentation

namespace IntegralModel

section Basic

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- Because `S.integer K` is Noetherian, any finite-type commutative Hopf algebra over
`S.integer K` with generic fibre `H` defines an `IntegralModel`. -/
def ofFiniteType (C : _root_.CommHopfAlgCat.{v} (S.integer K))
    [Algebra.FiniteType (S.integer K) C]
    (e : CommHopfAlgCat.baseChange (K := K) C ≅ _root_.CommHopfAlgCat.of K H) :
    IntegralModel R K H S :=
  letI : Algebra.FinitePresentation (S.integer K) C :=
    (Algebra.FinitePresentation.of_finiteType (R := S.integer K) (A := C)).mp inferInstance
  { coordinate := C, baseChangeIso := e }

/-- An `R`-model `C₀` of `H` over the base Dedekind domain `R` induces an `S`-integral model for
every set of places `S` by scalar extension along `R → S.integer K`. -/
noncomputable def ofBaseRing (S : Set (HeightOneSpectrum R))
    (C₀ : _root_.CommHopfAlgCat.{v} R) [Algebra.FiniteType R C₀]
    (e : CommHopfAlgCat.baseChange (K := K) C₀ ≅ _root_.CommHopfAlgCat.of K H) :
    IntegralModel R K H S :=
  letI : Algebra.FiniteType (S.integer K) (CommHopfAlgCat.baseChange (K := S.integer K) C₀) :=
    Algebra.FiniteType.baseChange (S.integer K)
  ofFiniteType (CommHopfAlgCat.baseChange (K := S.integer K) C₀)
    (CommHopfAlgCat.baseChangeTowerIso R K C₀ ≪≫ e)

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is automatically finitely
presented over `K`. -/
theorem finitePresentation_genericFiber (M : IntegralModel R K H S) :
    Algebra.FinitePresentation K H :=
  letI : Algebra.FinitePresentation K (K ⊗[S.integer K] M.coordinate) :=
    Algebra.FinitePresentation.baseChange K
  Algebra.FinitePresentation.equiv (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).toAlgEquiv

/-- The generic-fibre coordinate algebra `H` of an `IntegralModel` is automatically of finite type
over `K`. -/
theorem finiteType_genericFiber (M : IntegralModel R K H S) : Algebra.FiniteType K H := by
  have := M.finitePresentation_genericFiber
  infer_instance

/-- The canonical ring homomorphism embedding the integral coordinate ring `M.coordinate` into the
generic coordinate ring `H` via `m ↦ M.baseChangeIso.hom.hom (1 ⊗ₜ m)`. -/
noncomputable def embed (M : IntegralModel R K H S) : M.coordinate →+* H :=
  M.baseChangeIso.hom.hom.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := S.integer K) (A := K) (B := M.coordinate)).toRingHom

/-- `M.embed` sends `m : M.coordinate` to `M.baseChangeIso.hom.hom (1 ⊗ₜ m)`. -/
@[simp]
theorem embed_apply (M : IntegralModel R K H S) (m : M.coordinate) :
    M.embed m = M.baseChangeIso.hom.hom (1 ⊗ₜ[S.integer K] m) :=
  (rfl)

/-- On pure tensors `c ⊗ₜ m`, `M.baseChangeIso.hom.hom` acts as `c • M.embed m`. -/
theorem baseChangeIso_hom_tmul (M : IntegralModel R K H S) (c : K) (m : M.coordinate) :
    M.baseChangeIso.hom.hom (c ⊗ₜ[S.integer K] m) = c • M.embed m := by
  have hcm : (c ⊗ₜ[S.integer K] m : K ⊗[S.integer K] M.coordinate) =
      c • ((1 : K) ⊗ₜ[S.integer K] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hcm, map_smul, embed_apply]

end Basic

/-! ### Subgroups of points valued in an integral subring -/

section SubringPoints

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- Given a commutative `K`-algebra `A` and a subring `B : Subring A` containing the image of
`S.integer K`, `M.subringPoints B hB` is the subgroup of `WithConv (H →ₐ[K] A)` consisting of
points that arise from `B`-valued `(S.integer K)`-points of `M.coordinate`. -/
noncomputable def subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) :
    Subgroup (WithConv (H →ₐ[K] A)) :=
  letI : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  let eA : WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
    (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
      (BialgEquiv.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm)
  (eA.toMonoidHom.comp (AlgHom.mapValue (H := M.coordinate) ιB)).range

/-- A point `g : WithConv (H →ₐ[K] A)` belongs to `M.subringPoints B hB` if and only if it maps
every integral coordinate `M.embed m` (`m : M.coordinate`) into `B`. -/
@[simp]
theorem mem_subringPoints_iff (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    (B : Subring A) (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ B := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  let eA : WithConv (M.coordinate →ₐ[S.integer K] A) ≃* WithConv (H →ₐ[K] A) :=
    (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
      (BialgEquiv.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm)
  have hmem : g ∈ M.subringPoints B hB ↔
      eA.symm g ∈ MonoidHom.mrange (AlgHom.mapValue (H := M.coordinate) ιB) := by
    delta subringPoints
    -- Rebind the unfolded `let` expressions to the local `ιB` and `eA` before applying `mem_range`.
    change g ∈ (eA.toMonoidHom.comp (AlgHom.mapValue (H := M.coordinate) ιB)).range ↔ _
    rw [MonoidHom.mem_range, MonoidHom.mem_mrange]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, eA.eq_symm_apply.mpr hx⟩,
      fun ⟨x, hx⟩ ↦ ⟨x, by simpa [MonoidHom.comp_apply] using congrArg eA hx⟩⟩
  rw [hmem, AlgHom.mem_mrange_mapValue_iff B.subtype_injective]
  refine forall_congr' fun m ↦ ?_
  have heval : (eA.symm g).ofConv m = g.ofConv (M.embed m) := by
    simp [eA, embed_apply]
    rfl
  have hrange : (ιB.range : Set A) = (B : Set A) := Subtype.range_coe
  rw [heval, ← SetLike.mem_coe, hrange, SetLike.mem_coe]

/-- Membership in `M.subringPoints B hB` need only be checked on an `(S.integer K)`-algebra
generating family of `M.coordinate`. -/
theorem mem_subringPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {A : Type w} [CommRing A] [Algebra K A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B)
    {ι : Type*} {a : ι → M.coordinate} (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤)
    {g : WithConv (H →ₐ[K] A)} :
    g ∈ M.subringPoints B hB ↔ ∀ i, g.ofConv (M.embed (a i)) ∈ B := by
  rw [mem_subringPoints_iff]
  refine ⟨fun h i ↦ h (a i), fun h m ↦ ?_⟩
  have hm : m ∈ Algebra.adjoin (S.integer K) (Set.range a) := ha ▸ Algebra.mem_top
  refine Algebra.adjoin_induction ?_ ?_
    (fun _ _ _ _ hx hy ↦ by rw [map_add, map_add]; exact B.add_mem hx hy)
    (fun _ _ _ _ hx hy ↦ by rw [map_mul, map_mul]; exact B.mul_mem hx hy) hm
  · rintro _ ⟨i, rfl⟩
    exact h i
  · intro x
    have htmul : ((1 : K) ⊗ₜ[S.integer K] algebraMap (S.integer K) M.coordinate x) =
        ((x : K) ⊗ₜ[S.integer K] (1 : M.coordinate)) := by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
        smul_eq_mul, mul_one]
    have hx : M.embed (algebraMap (S.integer K) M.coordinate x) = algebraMap K H (x : K) := by
      rw [embed_apply, htmul, M.baseChangeIso_hom_tmul, map_one, Algebra.algebraMap_eq_smul_one]
    rw [hx, g.ofConv.commutes]
    exact hB x

/-- Topologically, the base-change isomorphism `WithConv (M.coordinate →ₐ[S.integer K] A) ≃*
WithConv (H →ₐ[K] A)` is a homeomorphism when `A` is a topological semiring. -/
private noncomputable def coordinatePointsContinuousMulEquiv (M : IntegralModel R K H S)
    (A : Type w) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalSemiring A] :
    WithConv (M.coordinate →ₐ[S.integer K] A) ≃ₜ* WithConv (H →ₐ[K] A) where
  toMulEquiv :=
    (AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate) (R := A)).trans
      (BialgEquiv.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm)
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
        simp [BialgEquiv.mapDomainMulEquiv_apply, BialgHom.mapDomain_apply]
  continuous_invFun := continuous_withConv_iff.2 fun m ↦ by
    have heval (g : WithConv (H →ₐ[K] A)) :
        ((((AlgHom.baseChangePointsMulEquiv (k := S.integer K) (K := K) (A := M.coordinate)
            (R := A)).trans
            (BialgEquiv.mapDomainMulEquiv (A := A)
              (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).symm)).symm g).ofConv m) =
          g.ofConv (M.embed m) := by
      simp [embed_apply]
      rfl
    simpa only [MulEquiv.invFun_eq_symm, heval] using continuous_eval_ofConv (M.embed m)

/-- When `B` is an open subring of a topological `K`-algebra `A`, `M.subringPoints B hB` is an open
subgroup of `WithConv (H →ₐ[K] A)`. -/
theorem isOpen_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBopen : IsOpen (B : Set A)) :
    IsOpen (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  have hι : IsOpenEmbedding ιB := hBopen.isOpenEmbedding_subtypeVal
  have hmap : IsOpenEmbedding (AlgHom.mapValue (H := M.coordinate) ιB) :=
    AlgHom.isOpenEmbedding_mapValue hι
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isOpenEmbedding.comp
    hmap).isOpen_range

/-- When `B` is a closed subring of a topological `K`-algebra `A`, `M.subringPoints B hB` is a
closed subgroup of `WithConv (H →ₐ[K] A)`. -/
theorem isClosed_subringPoints (M : IntegralModel R K H S) {A : Type w} [CommRing A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalSemiring A] (B : Subring A)
    (hB : ∀ x : S.integer K, algebraMap K A (x : K) ∈ B) (hBclosed : IsClosed (B : Set A)) :
    IsClosed (M.subringPoints B hB : Set (WithConv (H →ₐ[K] A))) := by
  let : Algebra (S.integer K) B := ((algebraMap (S.integer K) A).codRestrict B hB).toAlgebra
  let ιB : B →ₐ[S.integer K] A := { B.subtype with commutes' := fun _ ↦ rfl }
  have hι : IsClosedEmbedding ιB := hBclosed.isClosedEmbedding_subtypeVal
  have hmap : IsClosedEmbedding (AlgHom.mapValue (H := M.coordinate) ιB) :=
    AlgHom.isClosedEmbedding_mapValue hι
  exact ((M.coordinatePointsContinuousMulEquiv A).toHomeomorph.isClosedEmbedding.comp
    hmap).isClosed_range

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

end SubringPoints

/-! ### Local integral subgroups and reference level families -/

section LocalAndLevel

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- At a finite place `v ∉ S`, `M.localPoints v hv` is the subgroup `𝒢(𝒪_v) ≤ G(K_v)` of `v`-adic
points sending every integral coordinate `M.embed m` into `v.adicCompletionIntegers K`. -/
noncomputable def localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    (hv : v ∉ S) : Subgroup (LocalPoints K H v) :=
  M.subringPoints (v.adicCompletionIntegers K).toSubring fun x ↦ by
    rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact x.2 v hv

/-- A `v`-adic point belongs to `M.localPoints v hv` if and only if it evaluates every integral
coordinate into `v.adicCompletionIntegers K`. -/
@[simp]
theorem mem_localPoints_iff (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K H v} :
    g ∈ M.localPoints v hv ↔
      ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ v.adicCompletionIntegers K :=
  M.mem_subringPoints_iff (v.adicCompletionIntegers K).toSubring _

/-- Membership in `M.localPoints v hv` need only be checked on an `(S.integer K)`-algebra
generating family of `M.coordinate`. -/
theorem mem_localPoints_iff_of_adjoin_eq_top (M : IntegralModel R K H S)
    {v : HeightOneSpectrum R} (hv : v ∉ S) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (S.integer K) (Set.range a) = ⊤) {g : LocalPoints K H v} :
    g ∈ M.localPoints v hv ↔ ∀ i, g.ofConv (M.embed (a i)) ∈ v.adicCompletionIntegers K :=
  M.mem_subringPoints_iff_of_adjoin_eq_top (v.adicCompletionIntegers K).toSubring _ ha

/-- `M.localPoints v hv` is an open subgroup of `LocalPoints K H v`. -/
theorem isOpen_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsOpen (M.localPoints v hv : Set (LocalPoints K H v)) :=
  M.isOpen_subringPoints (v.adicCompletionIntegers K).toSubring _
    (Valued.isOpen_valuationSubring _)

/-- `M.localPoints v hv` is closed in `LocalPoints K H v`. -/
theorem isClosed_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    IsClosed (M.localPoints v hv : Set (LocalPoints K H v)) :=
  Subgroup.isClosed_of_isOpen (M.localPoints v hv) (M.isOpen_localPoints v hv)

/-- When the residue field `R ⧸ v.asIdeal` is finite (so `v.adicCompletion K` is a nonarchimedean
local field), `M.localPoints v hv` is a compact subgroup of `LocalPoints K H v`. -/
theorem isCompact_localPoints (M : IntegralModel R K H S) (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] (hv : v ∉ S) :
    IsCompact (M.localPoints v hv : Set (LocalPoints K H v)) := by
  let _ : CompactSpace (v.adicCompletionIntegers K) := inferInstance
  let _ : CompactSpace (v.adicCompletionIntegers K).toSubring :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  exact M.isCompact_subringPoints (v.adicCompletionIntegers K).toSubring _

open scoped Classical in
/-- The family of reference subgroups attached to `M` across all finite places: `M.localPoints v hv`
outside `S`, and the full local group `⊤` at the exceptional places `v ∈ S`. -/
noncomputable def level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    Subgroup (LocalPoints K H v) :=
  if hv : v ∈ S then ⊤ else M.localPoints v hv

/-- At an exceptional place `v ∈ S`, `M.level v` is the whole local group `⊤`. -/
@[simp]
theorem level_of_mem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∈ S) :
    M.level v = ⊤ := by
  delta level
  simp [hv]

/-- At a place `v ∉ S`, `M.level v` is `M.localPoints v hv`. -/
@[simp]
theorem level_of_notMem (M : IntegralModel R K H S) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    M.level v = M.localPoints v hv := by
  delta level
  simp [hv]

/-- Every reference subgroup `M.level v` is open in `LocalPoints K H v`. -/
theorem isOpen_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsOpen (M.level v : Set (LocalPoints K H v)) := by
  by_cases hv : v ∈ S
  · rw [M.level_of_mem hv]
    exact isOpen_univ
  · rw [M.level_of_notMem hv]
    exact M.isOpen_localPoints v hv

/-- Every reference subgroup `M.level v` is closed in `LocalPoints K H v`. -/
theorem isClosed_level (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    IsClosed (M.level v : Set (LocalPoints K H v)) :=
  Subgroup.isClosed_of_isOpen (M.level v) (M.isOpen_level v)

/-- `M.level v` bundled as an `OpenSubgroup` of `LocalPoints K H v`. -/
noncomputable def openLevel (M : IntegralModel R K H S) (v : HeightOneSpectrum R) :
    OpenSubgroup (LocalPoints K H v) :=
  ⟨M.level v, M.isOpen_level v⟩

/-- For an everywhere-integral model (`S = ∅`) over a Dedekind domain with finite residue fields,
`M.localPoints` packages as a `CompactOpenSubgroups` family across all finite places. -/
noncomputable def compactOpenSubgroups (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    CompactOpenSubgroups (LocalPoints (R := R) K H) where
  subgroup v := M.openLevel v
  isCompact_subgroup v := by
    -- Unfold the carrier of `M.openLevel v` to `M.level v` so `level_of_notMem` applies.
    change IsCompact (M.level v : Set (LocalPoints K H v))
    rw [M.level_of_notMem (Set.notMem_empty v)]
    exact M.isCompact_localPoints v (Set.notMem_empty v)

end LocalAndLevel

/-! ### Global `T`-integral subgroups -/

section GlobalPoints

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- For `T ⊇ S`, `M.globalPoints T hST` is the subgroup `𝒢(𝒪_{K,T}) ≤ G(K)` of `K`-rational points
sending every integral coordinate of `M` into `T.integer K`. -/
noncomputable def globalPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : Subgroup (WithConv (H →ₐ[K] K)) :=
  M.subringPoints (T.integer K).toSubring fun x v hv ↦ x.2 v fun hvS ↦ hv (hST hvS)

/-- A `K`-rational point lies in `M.globalPoints T hST` if and only if its values on `M.embed` lie
in `T.integer K`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔ ∀ m : M.coordinate, g.ofConv (M.embed m) ∈ T.integer K :=
  M.mem_subringPoints_iff (T.integer K).toSubring _

/-- Enlarging the allowed pole set `T` enlarges `M.globalPoints`. -/
theorem globalPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.globalPoints T₁ hST₁ ≤ M.globalPoints T₂ (hST₁.trans hT₁₂) := fun _ hg ↦ by
  rw [mem_globalPoints_iff] at hg ⊢
  exact fun m v hv ↦ hg m v fun hv₁ ↦ hv (hT₁₂ hv₁)

/-- **Local-global characterization of `T`-integral rational points**: a `K`-point lies in
`M.globalPoints T hST` if and only if its diagonal image at every place `v ∉ T` lies in
`M.localPoints v`. -/
theorem mem_globalPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {g : WithConv (H →ₐ[K] K)} :
    g ∈ M.globalPoints T hST ↔
      ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
        LocalPoints.diagonal K H v g ∈ M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_globalPoints_iff, Set.mem_integer_iff, mem_localPoints_iff,
    LocalPoints.diagonal_apply_ofConv, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

end GlobalPoints

/-! ### Enlarging the exceptional set of places -/

section Enlarge

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S S' : Set (HeightOneSpectrum R)}

/-- Extending scalars along `S.integer K → S'.integer K` (`S ⊆ S'`) produces an `S'`-integral
model of `H` whose generic-fibre identification factors through `baseChangeTowerIso`. -/
noncomputable def enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S') :
    IntegralModel R K H S' :=
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

/-- Enlarging the exceptional set preserves `subringPoints` for any subring containing the image of
`S'.integer K`. -/
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
          ((1 : K) ⊗ₜ[S'.integer K] (c ⊗ₜ[S.integer K] m))) =
      (c : K) • M.embed m
    rw [CommHopfAlgCat.baseChangeTowerIso_hom_apply, Algebra.smul_def, mul_one]
    exact M.baseChangeIso_hom_tmul (c : K) m
  rw [hM']
  ext g
  simp only [mem_subringPoints_iff]
  refine ⟨fun h m ↦ ?_, fun h t ↦ ?_⟩
  · simpa only [htmul 1 m, Subalgebra.coe_one, one_smul] using
      h ((1 : S'.integer K) ⊗ₜ[S.integer K] m)
  · refine TensorProduct.inductionOn t ?_ ?_
    · intro c m
      rw [htmul c m, map_smul, Algebra.smul_def]
      exact B.mul_mem (hB' c) (h m)
    · intro x y hx hy
      rw [map_add, map_add]
      exact B.add_mem hx hy

/-- Enlarging `S` to `S'` leaves `localPoints` unchanged at every place `v ∉ S'`. -/
@[simp]
theorem localPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (v : HeightOneSpectrum R) (hv : v ∉ S') :
    (M.enlarge hSS').localPoints v hv = M.localPoints v (fun hvS ↦ hv (hSS' hvS)) :=
  M.subringPoints_enlarge hSS' (v.adicCompletionIntegers K).toSubring _

/-- Enlarging `S` to `S'` leaves `level v` unchanged at every place `v ∉ S'`. -/
theorem level_enlarge_of_notMem (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    {v : HeightOneSpectrum R} (hv : v ∉ S') :
    (M.enlarge hSS').level v = M.level v := by
  rw [(M.enlarge hSS').level_of_notMem hv, M.level_of_notMem (fun hvS ↦ hv (hSS' hvS)),
    M.localPoints_enlarge hSS' v hv]

/-- Enlarging `S` to `S'` leaves `globalPoints T` unchanged for every `T ⊇ S'`. -/
@[simp]
theorem globalPoints_enlarge (M : IntegralModel R K H S) (hSS' : S ⊆ S')
    (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').globalPoints T hS'T = M.globalPoints T (hSS'.trans hS'T) :=
  M.subringPoints_enlarge hSS' (T.integer K).toSubring _

end Enlarge

/-! ### Eventual integrality and independence of the model -/

section EventualIndependence

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]

/-- For every fixed generic coordinate `h : H`, all but finitely many places `v` of `R` have the
property that if `v ∉ S`, every `g ∈ M.localPoints v hv` evaluates `h` into
`v.adicCompletionIntegers K`. The exceptional places are only those where the `K`-coefficients
needed to expand `h` in `K ⊗[S.integer K] M.coordinate` fail to be `v`-integral. -/
theorem eventually_localPoints_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (h : H) :
    ∀ᶠ v in cofinite, ∀ (hv : v ∉ S), ∀ g ∈ M.localPoints v hv,
      g.ofConv h ∈ v.adicCompletionIntegers K := by
  -- Express `h` as the image of `t = M.baseChangeIso.inv.hom h` in `K ⊗[S.integer K] M.coordinate`
  -- and induct on `t`.
  suffices ∀ t : K ⊗[S.integer K] M.coordinate,
      ∀ᶠ v in cofinite, ∀ (hv : v ∉ S), ∀ g ∈ M.localPoints v hv,
        g.ofConv (M.baseChangeIso.hom.hom t) ∈ v.adicCompletionIntegers K by
    have ht : M.baseChangeIso.hom.hom (M.baseChangeIso.inv.hom h) = h :=
      (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).apply_symm_apply h
    simpa only [ht] using this (M.baseChangeIso.inv.hom h)
  intro t
  refine TensorProduct.inductionOn t ?_ ?_
  · intro c m
    filter_upwards [(algebraMap K (FiniteAdeleRing R K) c).2] with v hc hv g hg
    rw [M.baseChangeIso_hom_tmul, map_smul, Algebra.smul_def]
    exact mul_mem hc ((M.mem_localPoints_iff hv).mp hg m)
  · intro x y hx hy
    filter_upwards [hx, hy] with v hvx hvy hv g hg
    rw [map_add, map_add]
    exact add_mem (hvx hv g hg) (hvy hv g hg)

/-- When the exceptional set `S` is finite, for every fixed `h : H`, at all but finitely many
places `v` every `g ∈ M.level v` sends `h` into `v.adicCompletionIntegers K`. -/
theorem eventually_level_ofConv_mem {S : Set (HeightOneSpectrum R)}
    (M : IntegralModel R K H S) (hS : S.Finite) (h : H) :
    ∀ᶠ v in cofinite, ∀ g ∈ M.level v, g.ofConv h ∈ v.adicCompletionIntegers K := by
  filter_upwards [hS.compl_mem_cofinite, M.eventually_localPoints_ofConv_mem h] with v hv hloc g hg
  rw [M.level_of_notMem hv] at hg
  exact hloc hv g hg

/-- If `S₁` is finite, then `M₁.level v ≤ M₂.level v` at all but finitely many places `v`. -/
theorem level_eventuallyLe {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂) (hS₁ : S₁.Finite) :
    ∀ᶠ v in cofinite, M₁.level v ≤ M₂.level v := by
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := S₂.integer K) (A := M₂.coordinate)
  have hgen : Algebra.adjoin (S₂.integer K) (Set.range ((↑) : F → M₂.coordinate)) = ⊤ := by
    simpa using hF
  have hall : ∀ᶠ v in cofinite, ∀ i : F, ∀ g ∈ M₁.level v,
      g.ofConv (M₂.embed (i : M₂.coordinate)) ∈ v.adicCompletionIntegers K :=
    eventually_all.mpr fun i ↦ M₁.eventually_level_ofConv_mem hS₁ (M₂.embed (i : M₂.coordinate))
  filter_upwards [hall] with v hv g hg
  by_cases hv₂ : v ∈ S₂
  · rw [M₂.level_of_mem hv₂]
    exact Subgroup.mem_top g
  · rw [M₂.level_of_notMem hv₂, M₂.mem_localPoints_iff_of_adjoin_eq_top hv₂ hgen]
    exact fun i ↦ hv i g hg

/-- **Independence of the integral model away from finitely many places** (Conrad 2012,
Proposition 3.3 / Remark 3.5): any two integral models `M₁` (over finite `S₁`) and `M₂` (over
finite `S₂`) of the same `K`-group `H` define equal local integral subgroups `M₁.level v =
M₂.level v` at all but finitely many finite places `v`. -/
theorem level_eventuallyEq {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) :
    ∀ᶠ v in cofinite, M₁.level v = M₂.level v := by
  filter_upwards [level_eventuallyLe M₁ M₂ hS₁, level_eventuallyLe M₂ M₁ hS₂] with v h₁₂ h₂₁
  exact le_antisymm h₁₂ h₂₁

end EventualIndependence

/-! ### Concrete models and dependence of `localPoints` on `baseChangeIso` -/

section ConcreteModels

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))

/-- The canonical `S`-integral model of the trivial group `Spec K`, with coordinate ring
`S.integer K`. -/
noncomputable def trivial : IntegralModel R K K S where
  coordinate := _root_.CommHopfAlgCat.of (S.integer K) (S.integer K)
  baseChangeIso :=
    _root_.CommHopfAlgCat.isoMk
      (BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.rid (S.integer K) K K) (by ext) (by ext))

/-- The standard `S`-integral model of `𝔾ₐ = Spec (SymmetricAlgebra K K)`, with coordinate Hopf
algebra `SymmetricAlgebra (S.integer K) (S.integer K)` and canonical base-change isomorphism
`AdditiveGroup.coordinateHopfAlgebraBaseChangeIso`. -/
noncomputable def additive : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeIso := AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K

/-- Scaling the primitive generator of `SymmetricAlgebra K K` by a unit `c : Kˣ` as an
automorphism in `CommHopfAlgCat K`. -/
private noncomputable def scaleGaIso {K : Type v} [Field K] (c : Kˣ) :
    AdditiveGroup.coordinateHopfAlgebra K ≅ AdditiveGroup.coordinateHopfAlgebra K :=
  _root_.CommHopfAlgCat.isoMk <|
    BialgEquiv.ofAlgEquiv (SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c))
      (by
        apply SymmetricAlgebra.algHom_ext
        ext
        simp [SymmetricAlgebra.counitAlgHom_eq, SymmetricAlgebra.map_apply_ι,
          Units.smul_def, SymmetricAlgebra.algebraMapInv_ι])
      (by
        apply SymmetricAlgebra.algHom_ext
        ext
        simp [SymmetricAlgebra.comul_ι, SymmetricAlgebra.map_apply_ι, Units.smul_def])

/-- The `c`-scaled `S`-integral model of `𝔾ₐ = Spec (SymmetricAlgebra K K)` (`c : Kˣ`): it has the
*same* integral coordinate Hopf algebra `AdditiveGroup.coordinateHopfAlgebra (S.integer K)` as
`IntegralModel.additive`, while its generic-fibre identification scales the additive generator by
`(c : K)`. -/
noncomputable def scaledAdditive (c : Kˣ) : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeIso :=
    AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K ≪≫ scaleGaIso c

variable {R K S}

/-- `(scaledAdditive R K S c).coordinate` is literally `(additive R K S).coordinate`. -/
@[simp]
theorem scaledAdditive_coordinate (c : Kˣ) :
    (scaledAdditive R K S c).coordinate = (additive R K S).coordinate :=
  (rfl)

/-- At a place `v ∉ S`, a local point `g` of `𝔾ₐ` lies in `(scaledAdditive R K S c).localPoints v
hv` if and only if `(c : K) * (gaPointsMulEquiv g).toAdd ∈ v.adicCompletionIntegers K`, i.e. the
parameter lies in the fractional ideal `c⁻¹ 𝒪_v`. -/
theorem mem_localPoints_scaledAdditive_iff (c : Kˣ) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K (SymmetricAlgebra K K) v} :
    g ∈ (scaledAdditive R K S c).localPoints v hv ↔
      algebraMap K (v.adicCompletion K) (c : K) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  let M : IntegralModel R K (SymmetricAlgebra K K) S :=
    { coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
      baseChangeIso :=
        AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K ≪≫ scaleGaIso c }
  have hM : scaledAdditive R K S c = M := rfl
  have hgen : Algebra.adjoin (S.integer K)
      (Set.range fun _ : Unit ↦ (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1 : M.coordinate)) =
        ⊤ := by
    have hspan : Submodule.span (S.integer K) (Set.range fun _ : Unit ↦ (1 : S.integer K)) = ⊤ := by
      rw [Set.range_const]
      exact Ideal.span_singleton_one
    exact SymmetricAlgebra.adjoin_range_ι_comp_eq_top_of_span_eq_top _ hspan
  have hembed : M.embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) =
      SymmetricAlgebra.ι K K (c : K) := by
    -- Unfold `M.embed` into the composite of `gaScalarTensorBialgEquiv` and `scaleGaIso c`.
    change (scaleGaIso c).hom.hom
        ((AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K))
          ((1 : K) ⊗ₜ[S.integer K] SymmetricAlgebra.ι (S.integer K) (S.integer K) 1)) = _
    rw [AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, map_one, one_smul]
    -- Unfold `scaleGaIso c` on the SymmetricAlgebra carrier so `mapEquiv_ι` applies.
    change SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c)
      (SymmetricAlgebra.ι K K 1) = _
    rw [SymmetricAlgebra.mapEquiv_ι, DistribMulAction.toLinearEquiv_apply, Units.smul_def,
      smul_eq_mul, mul_one]
  rw [hM, M.mem_localPoints_iff_of_adjoin_eq_top hv hgen, Unique.forall_iff, hembed]
  have hc : SymmetricAlgebra.ι K K (c : K) = (c : K) • SymmetricAlgebra.ι K K 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hc, map_smul, Algebra.smul_def, AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- At a place `v ∉ S`, a local point `g` of `𝔾ₐ` lies in `(additive R K S).localPoints v hv` if
and only if its additive parameter lies in `v.adicCompletionIntegers K`. -/
theorem mem_localPoints_additive_iff {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : LocalPoints K (SymmetricAlgebra K K) v} :
    g ∈ (additive R K S).localPoints v hv ↔
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  have heq : (additive R K S).localPoints v hv = (scaledAdditive R K S 1).localPoints v hv := by
    let M₀ : IntegralModel R K (SymmetricAlgebra K K) S :=
      { coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
        baseChangeIso := AdditiveGroup.coordinateHopfAlgebraBaseChangeIso.{v, 0} (S.integer K) K }
    have hM₀ : additive R K S = M₀ := rfl
    have hgen : Algebra.adjoin (S.integer K)
        (Set.range fun _ : Unit ↦
          (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1 : M₀.coordinate)) = ⊤ := by
      have hspan :
          Submodule.span (S.integer K) (Set.range fun _ : Unit ↦ (1 : S.integer K)) = ⊤ := by
        rw [Set.range_const]
        exact Ideal.span_singleton_one
      exact SymmetricAlgebra.adjoin_range_ι_comp_eq_top_of_span_eq_top _ hspan
    have hembed₀ : M₀.embed (SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) =
        SymmetricAlgebra.ι K K 1 := by
      -- Unfold `M₀.embed` to `gaScalarTensorBialgEquiv` on `(1 : K) ⊗ₜ ι 1`.
      change (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K))
        ((1 : K) ⊗ₜ[S.integer K] SymmetricAlgebra.ι (S.integer K) (S.integer K) 1) = _
      rw [AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, map_one, one_smul]
    ext x
    rw [hM₀, M₀.mem_localPoints_iff_of_adjoin_eq_top hv hgen, Unique.forall_iff, hembed₀,
      mem_localPoints_scaledAdditive_iff, Units.val_one,
      (algebraMap K (v.adicCompletion K)).map_one, one_mul,
      AdditiveGroup.toAdd_gaPointsMulEquiv]
  rw [heq, mem_localPoints_scaledAdditive_iff, Units.val_one, map_one, one_mul]

/-- **Local integral subgroups depend on `baseChangeIso`, not only on `coordinate`**
(Conrad 2012, Remark 3.5): for every Dedekind domain `(R, K)`, every `S`, and every place `v ∉ S`,
there exists a unit `c : Kˣ` such that `scaledAdditive R K S c` has the exact same integral
coordinate Hopf algebra as `additive R K S`, yet `(additive R K S).localPoints v hv` is a strict
subgroup of `(scaledAdditive R K S c).localPoints v hv`. -/
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
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval_lt.le
  refine ⟨c, rfl, lt_of_le_not_ge ?_ ?_⟩
  · intro g hg
    rw [mem_localPoints_additive_iff hv] at hg
    rw [mem_localPoints_scaledAdditive_iff c hv]
    exact mul_mem hc_mem hg
  · intro hle
    let g : LocalPoints K (SymmetricAlgebra K K) v :=
      (AdditiveGroup.gaPointsMulEquiv (R := K) (A := v.adicCompletion K)).symm
        (Multiplicative.ofAdd (algebraMap K (v.adicCompletion K) ((c⁻¹ : Kˣ) : K)))
    have hg_scaled : g ∈ (scaledAdditive R K S c).localPoints v hv := by
      rw [mem_localPoints_scaledAdditive_iff c hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
        ← map_mul, Units.mul_inv, map_one]
      exact one_mem _
    have hg_std : g ∈ (additive R K S).localPoints v hv := hle hg_scaled
    rw [mem_localPoints_additive_iff hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
      map_inv₀] at hg_std
    have hne : Valued.v (algebraMap K (v.adicCompletion K) (c : K)) ≠ 0 :=
      (Valued.v).ne_zero_iff.mpr ((algebraMap K (v.adicCompletion K)).injective.ne hc0)
    have hmul : (1 : WithZero (Multiplicative ℤ)) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (c : K)) := by
      have := mul_le_mul_of_nonneg_left hg_std
        (zero_le (a := Valued.v (algebraMap K (v.adicCompletion K) (c : K))))
      rwa [mul_inv_cancel₀ hne, mul_one] at this
    exact not_lt_of_ge hmul hval_lt

end ConcreteModels

end IntegralModel

end TauCeti
