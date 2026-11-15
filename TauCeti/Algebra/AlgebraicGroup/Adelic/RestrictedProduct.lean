/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Adelic.IntegralModel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Restricted-product presentation of finite and full adelic points

Let `R` be a Dedekind domain with fraction field `K`, let `H` be a commutative Hopf `K`-algebra,
and let `M : IntegralModel R K H S` be an integral model of `G = Spec H` over the ring of
`S`-integers `S.integer K` for a finite set of finite places `S : Set (HeightOneSpectrum R)`.

This file proves the **Weil–Grothendieck restricted-product comparison theorem** (Conrad 2012,
Theorems 3.4 and 3.6):

* evaluation at all finite places induces a topological group isomorphism
  `M.finiteAdelicPointsContinuousMulEquiv hS :
    FiniteAdelicPoints R K H ≃ₜ* Πʳ v, [LocalPoints K H v, (M.level v : Set (LocalPoints K H v))]`
  from the functor-of-points finite adelic group `G(𝔸_f)` onto the restricted product of the local
  groups `G(K_v)` with respect to the integral subgroups `M.level v` (`= M.localPoints v hv` for
  `v ∉ S` and `⊤` for `v ∈ S`);
* combining with the splitting `AdelicPoints.splittingContinuousMulEquiv` yields the full adelic
  topological group isomorphism
  `M.adelicPointsContinuousMulEquiv hS :
    AdelicPoints R K H ≃ₜ*
      InfinitePoints K H × Πʳ v, [LocalPoints K H v, (M.level v : Set (LocalPoints K H v))]`.

Both directions of the continuity proof avoid coordinates on an ambient affine space and instead
work intrinsically with the point topology:

* **Forward continuity**: for any `T ⊇ S`, the subgroup `M.sAdelicPoints T hST ≤
  FiniteAdelicPoints R K H` of points valued in the open subring `FiniteAdeleRing.sIntegralAdeles R
  K T` is open (`isOpen_sAdelicPoints`), and when `S` is finite the open subgroups `M.sAdelicPoints
  T hST` over finite `T ⊇ S` exhaust `FiniteAdelicPoints R K H` (`exists_finite_mem_sAdelicPoints`).
  On each such open subgroup (`T` finite), the tuple of local projections lands in the principal
  stage `Πʳ v, [LocalPoints K H v, M.level v]_[𝓟 Tᶜ]`, which carries the subspace topology of the
  product `∏_v LocalPoints K H v`.
* **Inverse continuity**: by `PointTopology.continuous_withConv_iff`, continuity into
  `WithConv (H →ₐ[K] FiniteAdeleRing R K)` reduces to continuity after evaluating at each fixed
  `h : H`, where the map is `RestrictedProduct.mapAlong` along `(g : LocalPoints K H v) ↦
  g.ofConv h` using `IntegralModel.eventually_level_ofConv_mem`.

Finally, for any two models `M₁` (over finite `S₁`) and `M₂` (over finite `S₂`) of the same
generic `K`-group `H`, the canonical change-of-reference-family isomorphism
`restrictedProductCongr M₁.level M₂.level (level_eventuallyEq M₁ M₂ hS₁ hS₂)` intertwines
`M₁.finiteAdelicPointsContinuousMulEquiv hS₁` and `M₂.finiteAdelicPointsContinuousMulEquiv hS₂`
(`restrictedProductCongr_comp_finiteAdelicPointsContinuousMulEquiv`).

## Main declarations

* `TauCeti.IntegralModel.sAdelicPoints`: the open subgroup of `T`-integral finite adelic points,
  with `isOpen_sAdelicPoints`, `isClosed_sAdelicPoints`, `isCompact_sAdelicPoints_empty`,
  `comap_diagonal_sAdelicPoints`, and `exists_finite_mem_sAdelicPoints`.
* `TauCeti.IntegralModel.finiteAdelicPointsContinuousMulEquiv`: the topological group isomorphism
  `G(𝔸_f) ≃ₜ* Πʳ v, [G(K_v), M.level v]` for finite `S`.
* `TauCeti.IntegralModel.map_sAdelicPoints_self`: `M.finiteAdelicPointsContinuousMulEquiv hS` maps
  `M.sAdelicPoints S Set.Subset.rfl` onto `integralSubgroup M.level`.
* `TauCeti.IntegralModel.adelicPointsContinuousMulEquiv`: the full adelic topological group
  isomorphism `G(𝔸) ≃ₜ* G(K_∞) × Πʳ v, [G(K_v), M.level v]` for finite `S`.
* `TauCeti.IntegralModel.restrictedProductCongr_comp_finiteAdelicPointsContinuousMulEquiv`:
  independence of the restricted-product presentation from the choice of integral model.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3, Thm. 3.4, and Thm. 3.6, pp. 4–7.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open Filter IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped RestrictedProduct

namespace TauCeti

namespace IntegralModel

universe u v

/-! ### `T`-integral finite adelic subgroups and open exhaustion -/

section SAdelicPoints

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- For `T ⊇ S`, `M.sAdelicPoints T hST` is the subgroup of `FiniteAdelicPoints R K H` consisting
of finite adelic points that arise from `(FiniteAdeleRing.sIntegralAdeles R K T)`-valued points of
`M.coordinate`. -/
noncomputable def sAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : Subgroup (FiniteAdelicPoints R K H) :=
  M.subringPoints (FiniteAdeleRing.sIntegralAdeles R K T).toSubring fun x ↦
    (FiniteAdeleRing.algebraMap_mem_sIntegralAdeles_iff T (x : K)).mpr
      (fun v hv ↦ x.2 v fun hvS ↦ hv (hST hvS))

/-- A finite adelic point lies in `M.sAdelicPoints T hST` if and only if it maps every integral
coordinate of `M` into `FiniteAdeleRing.sIntegralAdeles R K T`. -/
@[simp]
theorem mem_sAdelicPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {x : FiniteAdelicPoints R K H} :
    x ∈ M.sAdelicPoints T hST ↔
      ∀ m : M.coordinate, x.ofConv (M.embed m) ∈ FiniteAdeleRing.sIntegralAdeles R K T :=
  M.mem_subringPoints_iff (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _

/-- Place-by-place characterization of `M.sAdelicPoints T hST`: a finite adelic point is
`T`-integral with respect to `M` if and only if its local projection at every place `v ∉ T` belongs
to `M.localPoints v`. -/
theorem mem_sAdelicPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {x : FiniteAdelicPoints R K H} :
    x ∈ M.sAdelicPoints T hST ↔
      ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
        FiniteAdelicPoints.localProjection R K H v x ∈
          M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_sAdelicPoints_iff, FiniteAdeleRing.mem_sIntegralAdeles, mem_localPoints_iff,
    FiniteAdelicPoints.localProjection_apply_ofConv]
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

/-- Every `T`-integral finite adelic subgroup `M.sAdelicPoints T hST` is open in
`FiniteAdelicPoints R K H`. -/
theorem isOpen_sAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) :
    IsOpen (M.sAdelicPoints T hST : Set (FiniteAdelicPoints R K H)) :=
  M.isOpen_subringPoints (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _
    (FiniteAdeleRing.isOpen_sIntegralAdeles R K T)

/-- Every `T`-integral finite adelic subgroup `M.sAdelicPoints T hST` is closed in
`FiniteAdelicPoints R K H`. -/
theorem isClosed_sAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) :
    IsClosed (M.sAdelicPoints T hST : Set (FiniteAdelicPoints R K H)) :=
  Subgroup.isClosed_of_isOpen (M.sAdelicPoints T hST) (M.isOpen_sAdelicPoints T hST)

/-- For an everywhere-integral model (`S = ∅`) over a Dedekind domain with finite residue fields,
the everywhere-integral finite adelic subgroup `M.sAdelicPoints ∅ Set.Subset.rfl` is compact. -/
theorem isCompact_sAdelicPoints_empty (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    IsCompact (M.sAdelicPoints ∅ Set.Subset.rfl : Set (FiniteAdelicPoints R K H)) := by
  have hcomp : IsCompact
      (FiniteAdeleRing.sIntegralAdeles R K ∅ : Set (FiniteAdeleRing R K)) := by
    rw [FiniteAdeleRing.sIntegralAdeles_empty]
    exact FiniteAdeleRing.isCompact_integralAdeles
  let _ : CompactSpace (FiniteAdeleRing.sIntegralAdeles R K ∅).toSubring :=
    isCompact_iff_compactSpace.mp hcomp
  exact M.isCompact_subringPoints (FiniteAdeleRing.sIntegralAdeles R K ∅).toSubring _

/-- Enlarging `S` to `S'` preserves `sAdelicPoints T` for every `T ⊇ S'`. -/
@[simp]
theorem sAdelicPoints_enlarge {S' : Set (HeightOneSpectrum R)} (M : IntegralModel R K H S)
    (hSS' : S ⊆ S') (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').sAdelicPoints T hS'T = M.sAdelicPoints T (hSS'.trans hS'T) :=
  M.subringPoints_enlarge hSS' (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _

/-- Enlarging the allowed pole set `T` enlarges `M.sAdelicPoints`. -/
theorem sAdelicPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.sAdelicPoints T₁ hST₁ ≤ M.sAdelicPoints T₂ (hST₁.trans hT₁₂) := fun _ hx ↦ by
  rw [mem_sAdelicPoints_iff] at hx ⊢
  exact fun m ↦ FiniteAdeleRing.sIntegralAdeles_mono R K hT₁₂ (hx m)

/-- Pulling back `M.sAdelicPoints T hST` along the diagonal `G(K) →* G(𝔸_f)` recovers the global
`T`-integral subgroup `M.globalPoints T hST`: `G(K) ∩ 𝒢(𝔸_{f,T}) = 𝒢(𝒪_{K,T})`. -/
@[simp]
theorem comap_diagonal_sAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) :
    (M.sAdelicPoints T hST).comap (FiniteAdelicPoints.diagonal R K H) =
      M.globalPoints T hST := by
  ext g
  simp [mem_sAdelicPoints_iff, mem_globalPoints_iff]

/-- **Exhaustion of `G(𝔸_f)` by open `T`-integral subgroups**: when `S` is finite, every finite
adelic point `x : FiniteAdelicPoints R K H` belongs to `M.sAdelicPoints T hST` for some finite set
of places `T ⊇ S`. -/
theorem exists_finite_mem_sAdelicPoints (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) :
    ∃ (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T), T.Finite ∧ x ∈ M.sAdelicPoints T hST := by
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := S.integer K) (A := M.coordinate)
  have hgen : Algebra.adjoin (S.integer K) (Set.range ((↑) : F → M.coordinate)) = ⊤ := by
    simpa using hF
  choose U hU using fun i : F ↦
    FiniteAdeleRing.exists_finset_mem_sIntegralAdeles (x.ofConv (M.embed (i : M.coordinate)))
  refine ⟨S ∪ ⋃ i : F, (U i : Set (HeightOneSpectrum R)), Set.subset_union_left,
    hS.union (Set.finite_iUnion fun i ↦ (U i).finite_toSet), ?_⟩
  rw [sAdelicPoints, M.mem_subringPoints_iff_of_adjoin_eq_top _ _ hgen]
  exact fun i ↦ FiniteAdeleRing.sIntegralAdeles_mono R K
    ((Set.subset_iUnion (fun j : F ↦ (U j : Set (HeightOneSpectrum R))) i).trans
      Set.subset_union_right)
    (hU i)

/-- When `S` is finite, the open subgroups `M.sAdelicPoints T hST` indexed by finite `T ⊇ S`
generate the whole group `FiniteAdelicPoints R K H` (in fact their directed union is `⊤`). -/
theorem iSup_sAdelicPoints_eq_top (M : IntegralModel R K H S) (hS : S.Finite) :
    (⨆ T : {T : Set (HeightOneSpectrum R) // S ⊆ T ∧ T.Finite},
      M.sAdelicPoints T.1 T.2.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨T, hST, hT, hx⟩ := M.exists_finite_mem_sAdelicPoints hS x
  exact Subgroup.mem_iSup_of_mem ⟨T, hST, hT⟩ hx

end SAdelicPoints

/-! ### Restricted-product comparison isomorphisms -/

section Comparison

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type v} [CommRing H] [HopfAlgebra K H]
  {S : Set (HeightOneSpectrum R)}

/-- When `S` is finite, the local projections of any finite adelic point `x` belong to `M.level v`
at all but finitely many places `v`. -/
theorem eventually_localProjection_mem_level (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) :
    ∀ᶠ v in cofinite, FiniteAdelicPoints.localProjection R K H v x ∈ M.level v := by
  obtain ⟨T, hST, hT, hx⟩ := M.exists_finite_mem_sAdelicPoints hS x
  filter_upwards [hT.compl_mem_cofinite] with v hv
  have hvS : v ∉ S := fun hvS ↦ hv (hST hvS)
  rw [M.level_of_notMem hvS]
  exact (M.mem_sAdelicPoints_iff_forall_localPoints hST).mp hx v hv

/-- Forward group homomorphism `G(𝔸_f) →* Πʳ v, [G(K_v), M.level v]` assembling all local
projections. -/
private noncomputable def toRestrictedProductMonoidHom (M : IntegralModel R K H S)
    (hS : S.Finite) :
    FiniteAdelicPoints R K H →* RestrictedProductGroup M.level where
  toFun x := ⟨fun v ↦ FiniteAdelicPoints.localProjection R K H v x,
    M.eventually_localProjection_mem_level hS x⟩
  map_one' := DFunLike.ext _ _ fun v ↦ map_one (FiniteAdelicPoints.localProjection R K H v)
  map_mul' x y := DFunLike.ext _ _ fun v ↦ map_mul (FiniteAdelicPoints.localProjection R K H v) x y

private theorem continuous_toRestrictedProductMonoidHom (M : IntegralModel R K H S)
    (hS : S.Finite) :
    Continuous (M.toRestrictedProductMonoidHom hS) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨T, hST, hT, hx₀⟩ := M.exists_finite_mem_sAdelicPoints hS x₀
  let U : Set (FiniteAdelicPoints R K H) := M.sAdelicPoints T hST
  have hU_nhds : U ∈ 𝓝 x₀ := (M.isOpen_sAdelicPoints T hST).mem_nhds hx₀
  have hT_cof : (cofinite : Filter (HeightOneSpectrum R)) ≤ 𝓟 Tᶜ :=
    le_principal_iff.mpr hT.compl_mem_cofinite
  let stage : U → Πʳ v, [LocalPoints K H v, (M.level v : Set (LocalPoints K H v))]_[𝓟 Tᶜ] :=
    fun u ↦ ⟨fun v ↦ FiniteAdelicPoints.localProjection R K H v u.1,
      eventually_principal.mpr fun v hv ↦ by
        dsimp only
        have hvS : v ∉ S := fun hvS ↦ hv (hST hvS)
        rw [SetLike.mem_coe, M.level_of_notMem hvS]
        exact (M.mem_sAdelicPoints_iff_forall_localPoints hST).mp u.2 v hv⟩
  have hstage : Continuous stage :=
    RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun v ↦
      (FiniteAdelicPoints.continuous_localProjection v).comp continuous_subtype_val
  have hrestr : Continuous (U.domRestrict (M.toRestrictedProductMonoidHom hS)) :=
    (RestrictedProduct.continuous_inclusion hT_cof).comp hstage
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestr).continuousAt hU_nhds

/-- Evaluation of a restricted-product tuple `y` at a fixed generic coordinate `h : H`, producing
an element of `FiniteAdeleRing R K` via `RestrictedProduct.mapAlong`. -/
private noncomputable def evalRestrictedProductAdele (M : IntegralModel R K H S) (hS : S.Finite)
    (h : H) : RestrictedProductGroup M.level → FiniteAdeleRing R K :=
  RestrictedProduct.mapAlong
    (fun v : HeightOneSpectrum R ↦ LocalPoints K H v)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (A₁ := fun v : HeightOneSpectrum R ↦ (M.level v : Set (LocalPoints K H v)))
    (A₂ := fun v : HeightOneSpectrum R ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (id : HeightOneSpectrum R → HeightOneSpectrum R)
    (tendsto_id : Tendsto id cofinite cofinite)
    (fun _ g ↦ g.ofConv h)
    (M.eventually_level_ofConv_mem hS h)

private theorem continuous_evalRestrictedProductAdele (M : IntegralModel R K H S) (hS : S.Finite)
    (h : H) : Continuous (M.evalRestrictedProductAdele hS h) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum R ↦ LocalPoints K H v)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (A₁ := fun v : HeightOneSpectrum R ↦ (M.level v : Set (LocalPoints K H v)))
    (A₂ := fun v : HeightOneSpectrum R ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (id : HeightOneSpectrum R → HeightOneSpectrum R)
    (tendsto_id : Tendsto id cofinite cofinite)
    (fun _ g ↦ g.ofConv h)
    (M.eventually_level_ofConv_mem hS h)
    (fun _ ↦ continuous_eval_ofConv h)

/-- Inverse map `Πʳ v, [G(K_v), M.level v] → G(𝔸_f)` assembling a compatible family of local
points into an `𝔸_f`-valued `K`-algebra homomorphism on `H`. -/
private noncomputable def ofRestrictedProduct (M : IntegralModel R K H S) (hS : S.Finite)
    (y : RestrictedProductGroup M.level) : FiniteAdelicPoints R K H :=
  toConv
    { toFun := fun h ↦ M.evalRestrictedProductAdele hS h y
      map_one' := FiniteAdeleRing.ext K fun v ↦ map_one (y v).ofConv
      map_mul' := fun a b ↦ FiniteAdeleRing.ext K fun v ↦ map_mul (y v).ofConv a b
      map_zero' := FiniteAdeleRing.ext K fun v ↦ map_zero (y v).ofConv
      map_add' := fun a b ↦ FiniteAdeleRing.ext K fun v ↦ map_add (y v).ofConv a b
      commutes' := fun k ↦ FiniteAdeleRing.ext K fun v ↦ by
        -- Unfold `M.evalRestrictedProductAdele hS (algebraMap K H k) y v` to `(y v).ofConv _`.
        change (y v).ofConv (algebraMap K H k) = algebraMap K (FiniteAdeleRing R K) k v
        rw [(y v).ofConv.commutes, FiniteAdeleRing.algebraMap_apply,
          HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
          Algebra.algebraMap_self_apply] }

/-- **Restricted-product presentation of finite adelic points** (Conrad 2012, Theorem 3.4): given
an integral model `M : IntegralModel R K H S` over a finite set of finite places `S`, assembling
the local projections defines a topological group isomorphism
`FiniteAdelicPoints R K H ≃ₜ* RestrictedProductGroup M.level`. -/
noncomputable def finiteAdelicPointsContinuousMulEquiv (M : IntegralModel R K H S)
    (hS : S.Finite) :
    FiniteAdelicPoints R K H ≃ₜ* RestrictedProductGroup M.level where
  toFun := M.toRestrictedProductMonoidHom hS
  invFun := M.ofRestrictedProduct hS
  left_inv x := WithConv.ofConv_injective <| AlgHom.ext fun h ↦ FiniteAdeleRing.ext K fun v ↦
    FiniteAdelicPoints.localProjection_apply_ofConv v x h
  right_inv y := DFunLike.ext _ _ fun v ↦ WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    FiniteAdelicPoints.localProjection_apply_ofConv v (M.ofRestrictedProduct hS y) h
  map_mul' := (M.toRestrictedProductMonoidHom hS).map_mul'
  continuous_toFun := M.continuous_toRestrictedProductMonoidHom hS
  continuous_invFun := continuous_withConv_iff.mpr fun h ↦
    M.continuous_evalRestrictedProductAdele hS h

/-- At each finite place `v`, `M.finiteAdelicPointsContinuousMulEquiv hS x v` is the local
projection `FiniteAdelicPoints.localProjection R K H v x`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS x v =
      FiniteAdelicPoints.localProjection R K H v x :=
  (rfl)

/-- Evaluating the `v`-component of `M.finiteAdelicPointsContinuousMulEquiv hS x` on `h : H`
reads off the `v`-coordinate `(x.ofConv h) v`. -/
theorem finiteAdelicPointsContinuousMulEquiv_apply_ofConv (M : IntegralModel R K H S)
    (hS : S.Finite) (x : FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) (h : H) :
    (M.finiteAdelicPointsContinuousMulEquiv hS x v).ofConv h = x.ofConv h v :=
  FiniteAdelicPoints.localProjection_apply_ofConv v x h

/-- Evaluating `(M.finiteAdelicPointsContinuousMulEquiv hS).symm y` at `h : H` and `v` gives
`(y v).ofConv h`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    (hS : S.Finite) (y : RestrictedProductGroup M.level) (h : H) (v : HeightOneSpectrum R) :
    ((M.finiteAdelicPointsContinuousMulEquiv hS).symm y).ofConv h v = (y v).ofConv h :=
  (rfl)

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` intertwines the global-to-finite-adelic diagonal
with the local diagonals `LocalPoints.diagonal K H v`. -/
theorem finiteAdelicPointsContinuousMulEquiv_diagonal (M : IntegralModel R K H S) (hS : S.Finite)
    (g : WithConv (H →ₐ[K] K)) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS (FiniteAdelicPoints.diagonal R K H g) v =
      LocalPoints.diagonal K H v g := by
  simp

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` maps the `S`-integral finite adelic subgroup
`M.sAdelicPoints S Set.Subset.rfl` onto the everywhere-level subgroup `integralSubgroup M.level`
($\prod_{v \in S} G(K_v) \times \prod_{v \notin S} \mathcal{G}(\mathcal{O}_v)$). -/
@[simp]
theorem map_sAdelicPoints_self (M : IntegralModel R K H S) (hS : S.Finite) :
    (M.sAdelicPoints S Set.Subset.rfl).map
        ((M.finiteAdelicPointsContinuousMulEquiv hS :
          FiniteAdelicPoints R K H ≃* RestrictedProductGroup M.level) :
          FiniteAdelicPoints R K H →* RestrictedProductGroup M.level) =
      integralSubgroup M.level := by
  ext y
  rw [Subgroup.mem_map, mem_integralSubgroup]
  refine ⟨?_, fun hy ↦ ⟨(M.finiteAdelicPointsContinuousMulEquiv hS).symm y, ?_,
    (M.finiteAdelicPointsContinuousMulEquiv hS).apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩ v
    by_cases hv : v ∈ S
    · rw [M.level_of_mem hv]
      exact Subgroup.mem_top _
    · rw [M.level_of_notMem hv]
      exact (M.mem_sAdelicPoints_iff_forall_localPoints Set.Subset.rfl).mp hx v hv
  · rw [M.mem_sAdelicPoints_iff_forall_localPoints Set.Subset.rfl]
    intro v hv
    have hv' := hy v
    rw [M.level_of_notMem hv] at hv'
    have hproj : FiniteAdelicPoints.localProjection R K H v
        ((M.finiteAdelicPointsContinuousMulEquiv hS).symm y) = y v := by
      ext h
      simp
    rwa [hproj]

/-- **Restricted-product presentation of full adelic points** (Conrad 2012, Theorem 3.6): given
an integral model `M : IntegralModel R K H S` over a finite set of finite places `S`, the full
adelic group `AdelicPoints R K H` is canonically isomorphic as a topological group to
`InfinitePoints K H × Πʳ v, [LocalPoints K H v, M.level v]`. -/
noncomputable def adelicPointsContinuousMulEquiv (M : IntegralModel R K H S) (hS : S.Finite) :
    AdelicPoints R K H ≃ₜ*
      RestrictedProductGroupWithFactor (InfinitePoints K H) M.level :=
  (AdelicPoints.splittingContinuousMulEquiv R K H).trans
    { (MulEquiv.refl (InfinitePoints K H)).prodCongr
        (M.finiteAdelicPointsContinuousMulEquiv hS).toMulEquiv with
      continuous_toFun := continuous_fst.prodMk
        ((M.finiteAdelicPointsContinuousMulEquiv hS).continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk
        ((M.finiteAdelicPointsContinuousMulEquiv hS).symm.continuous.comp continuous_snd) }

/-- The archimedean component of `M.adelicPointsContinuousMulEquiv hS x` is
`AdelicPoints.infiniteProjection R K H x`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_fst (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints R K H) :
    (M.adelicPointsContinuousMulEquiv hS x).1 = AdelicPoints.infiniteProjection R K H x :=
  AdelicPoints.splittingContinuousMulEquiv_fst x

/-- The finite-place restricted-product component of `M.adelicPointsContinuousMulEquiv hS x` is
`M.finiteAdelicPointsContinuousMulEquiv hS (AdelicPoints.finiteProjection R K H x)`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_snd (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints R K H) :
    (M.adelicPointsContinuousMulEquiv hS x).2 =
      M.finiteAdelicPointsContinuousMulEquiv hS (AdelicPoints.finiteProjection R K H x) :=
  congrArg (M.finiteAdelicPointsContinuousMulEquiv hS)
    (AdelicPoints.splittingContinuousMulEquiv_snd x)

/-- **Model independence of the restricted-product presentation** (Conrad 2012, Proposition 3.3 and
Theorem 3.4): for any two integral models `M₁` (over finite `S₁`) and `M₂` (over finite `S₂`) of
the same generic `K`-group `H`, the change-of-reference-family isomorphism
`restrictedProductCongr M₁.level M₂.level (level_eventuallyEq M₁ M₂ hS₁ hS₂)` carries
`M₁.finiteAdelicPointsContinuousMulEquiv hS₁` to `M₂.finiteAdelicPointsContinuousMulEquiv hS₂`. -/
@[simp]
theorem restrictedProductCongr_comp_finiteAdelicPointsContinuousMulEquiv
    {S₁ S₂ : Set (HeightOneSpectrum R)}
    (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) (x : FiniteAdelicPoints R K H) :
    restrictedProductCongr M₁.level M₂.level (level_eventuallyEq M₁ M₂ hS₁ hS₂)
        (M₁.finiteAdelicPointsContinuousMulEquiv hS₁ x) =
      M₂.finiteAdelicPointsContinuousMulEquiv hS₂ x :=
  DFunLike.ext _ _ fun v ↦ by simp

end Comparison

end IntegralModel

end TauCeti
