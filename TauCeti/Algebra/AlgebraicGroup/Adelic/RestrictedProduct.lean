/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Adelic.IntegralModel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Restricted-product presentation of finite-adelic and `𝔸[R, K]`-valued points

For `M : IntegralModel R K H S` with `S.Finite`, this file proves the Weil–Grothendieck
restricted-product comparison (Conrad 2012, Theorems 3.4 and 3.6):
* `M.finiteAdelicPointsContinuousMulEquiv hS : FiniteAdelicPoints R K H ≃ₜ*
  RestrictedProductGroup M.level`, mapping `M.sIntegralAdelicPoints S Set.Subset.rfl` onto
  `integralSubgroup M.level`;
* `M.adelicPointsContinuousMulEquiv hS : AdelicPoints R K H ≃ₜ*
  RestrictedProductGroupWithFactor (InfinitePoints K H) M.level`;
* `restrictedProductCongr_finiteAdelicPointsContinuousMulEquiv`: model independence.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3, Thm. 3.4, and Thm. 3.6, pp. 4–7.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open Filter IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped RestrictedProduct

namespace TauCeti.IntegralModel

universe u v uH

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type uH} [CommRing H] [HopfAlgebra K H] {S : Set (HeightOneSpectrum R)}

/-- For `T ⊇ S`, `M.sIntegralAdelicPoints T hST` is the subgroup of `FiniteAdelicPoints R K H`
arising from `(FiniteAdeleRing.sIntegralAdeles R K T)`-valued points of `M.coordinate`. -/
noncomputable def sIntegralAdelicPoints (M : IntegralModel R K H S)
    (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) : Subgroup (FiniteAdelicPoints R K H) :=
  M.subringPoints (FiniteAdeleRing.sIntegralAdeles R K T).toSubring fun x ↦
    (FiniteAdeleRing.algebraMap_mem_sIntegralAdeles_iff T (x : K)).mpr (Set.integer_mono K hST x.2)

/-- `x ∈ M.sIntegralAdelicPoints T hST` iff `x` maps `M.embed` into
`FiniteAdeleRing.sIntegralAdeles`. -/
@[simp]
theorem mem_sIntegralAdelicPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {x : FiniteAdelicPoints R K H} :
    x ∈ M.sIntegralAdelicPoints T hST ↔
      ∀ m : M.coordinate, x.ofConv (M.embed m) ∈ FiniteAdeleRing.sIntegralAdeles R K T :=
  M.mem_subringPoints_iff (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _

/-- `x ∈ M.sIntegralAdelicPoints T hST` iff its projection at every `v ∉ T` lies in
`M.localPoints`. -/
theorem mem_sIntegralAdelicPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {x : FiniteAdelicPoints R K H} :
    x ∈ M.sIntegralAdelicPoints T hST ↔ ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
      FiniteAdelicPoints.localProjection R K H v x ∈ M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_sIntegralAdelicPoints_iff, FiniteAdeleRing.mem_sIntegralAdeles,
    mem_localPoints_iff, FiniteAdelicPoints.localProjection_apply_ofConv]
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

/-- Every `M.sIntegralAdelicPoints T hST` is open in `FiniteAdelicPoints R K H`. -/
theorem isOpen_sIntegralAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : IsOpen (M.sIntegralAdelicPoints T hST : Set (FiniteAdelicPoints R K H)) :=
  M.isOpen_subringPoints (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _
    (FiniteAdeleRing.isOpen_sIntegralAdeles R K T)

/-- Every `M.sIntegralAdelicPoints T hST` is closed in `FiniteAdelicPoints R K H`. -/
theorem isClosed_sIntegralAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) : IsClosed (M.sIntegralAdelicPoints T hST : Set (FiniteAdelicPoints R K H)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_sIntegralAdelicPoints T hST)

/-- For `S = ∅` and finite residue fields, `M.sIntegralAdelicPoints ∅ Set.Subset.rfl` is
compact. -/
theorem isCompact_sIntegralAdelicPoints_empty
    (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    IsCompact (M.sIntegralAdelicPoints ∅ Set.Subset.rfl : Set (FiniteAdelicPoints R K H)) := by
  let _ : CompactSpace (FiniteAdeleRing.sIntegralAdeles R K ∅).toSubring :=
    isCompact_iff_compactSpace.mp
      (FiniteAdeleRing.sIntegralAdeles_empty R K ▸ FiniteAdeleRing.isCompact_integralAdeles)
  exact M.isCompact_subringPoints _ _

/-- Enlarging `S` to `S'` preserves `sIntegralAdelicPoints T` for every `T ⊇ S'`. -/
@[simp]
theorem sIntegralAdelicPoints_enlarge {S' : Set (HeightOneSpectrum R)} (M : IntegralModel R K H S)
    (hSS' : S ⊆ S') (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').sIntegralAdelicPoints T hS'T =
      M.sIntegralAdelicPoints T (hSS'.trans hS'T) :=
  M.subringPoints_enlarge hSS' (FiniteAdeleRing.sIntegralAdeles R K T).toSubring _

/-- Enlarging `T` enlarges `M.sIntegralAdelicPoints`. -/
theorem sIntegralAdelicPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.sIntegralAdelicPoints T₁ hST₁ ≤ M.sIntegralAdelicPoints T₂ (hST₁.trans hT₁₂) := fun _ hx ↦
  (mem_sIntegralAdelicPoints_iff M _).mpr fun m ↦
    FiniteAdeleRing.sIntegralAdeles_mono R K hT₁₂ ((mem_sIntegralAdelicPoints_iff M _).mp hx m)

/-- Pulling back `M.sIntegralAdelicPoints T hST` along `diagonal` recovers `M.globalPoints T`. -/
@[simp]
theorem comap_diagonal_sIntegralAdelicPoints (M : IntegralModel R K H S)
    (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) :
    (M.sIntegralAdelicPoints T hST).comap (FiniteAdelicPoints.diagonal R K H) =
      M.globalPoints T hST := by ext g; simp [mem_sIntegralAdelicPoints_iff, mem_globalPoints_iff]

/-- Exhaustion of `G(𝔸ᶠ[R, K])` by open `T`-integral subgroups for finite `T ⊇ S` when `S` is
finite. -/
theorem exists_finite_mem_sIntegralAdelicPoints (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) :
    ∃ (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T),
      T.Finite ∧ x ∈ M.sIntegralAdelicPoints T hST := by
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := S.integer K) (A := M.coordinate)
  have hgen : Algebra.adjoin (S.integer K) (Set.range ((↑) : F → M.coordinate)) = ⊤ := by
    simpa using hF
  choose U hU using fun i : F ↦
    FiniteAdeleRing.exists_finset_mem_sIntegralAdeles (x.ofConv (M.embed i))
  refine ⟨S ∪ ⋃ i : F, (U i : Set (HeightOneSpectrum R)), Set.subset_union_left,
    hS.union (Set.finite_iUnion fun i ↦ (U i).finite_toSet), ?_⟩
  rw [sIntegralAdelicPoints, M.mem_subringPoints_iff_of_adjoin_eq_top _ _ hgen]
  exact fun i ↦ FiniteAdeleRing.sIntegralAdeles_mono R K
    ((Set.subset_iUnion (fun j : F ↦ (U j : Set (HeightOneSpectrum R))) i).trans
      Set.subset_union_right) (hU i)

/-- When `S` is finite, `⨆_{T ⊇ S finite} M.sIntegralAdelicPoints T = ⊤`. -/
theorem iSup_sIntegralAdelicPoints_eq_top (M : IntegralModel R K H S) (hS : S.Finite) :
    (⨆ T : {T : Set (HeightOneSpectrum R) // S ⊆ T ∧ T.Finite},
      M.sIntegralAdelicPoints T.1 T.2.1) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ let ⟨T, hST, hT, hx⟩ := M.exists_finite_mem_sIntegralAdelicPoints hS x
    Subgroup.mem_iSup_of_mem ⟨T, hST, hT⟩ hx

/-- When `S` is finite, `localProjection v x ∈ M.level v` at all but finitely many places `v`. -/
theorem eventually_localProjection_mem_level (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) :
    ∀ᶠ v in cofinite, FiniteAdelicPoints.localProjection R K H v x ∈ M.level v := by
  obtain ⟨T, hST, hT, hx⟩ := M.exists_finite_mem_sIntegralAdelicPoints hS x
  filter_upwards [hT.compl_mem_cofinite] with v hv
  rw [M.level_of_notMem (fun hvS ↦ hv (hST hvS))]
  exact (M.mem_sIntegralAdelicPoints_iff_forall_localPoints hST).mp hx v hv

private noncomputable def toRestrictedProductMonoidHom (M : IntegralModel R K H S)
    (hS : S.Finite) : FiniteAdelicPoints R K H →* RestrictedProductGroup M.level where
  toFun x := ⟨fun v ↦ FiniteAdelicPoints.localProjection R K H v x,
    M.eventually_localProjection_mem_level hS x⟩
  map_one' := DFunLike.ext _ _ fun v ↦ map_one (FiniteAdelicPoints.localProjection R K H v)
  map_mul' x y := DFunLike.ext _ _ fun v ↦ map_mul (FiniteAdelicPoints.localProjection R K H v) x y

private theorem continuous_toRestrictedProductMonoidHom (M : IntegralModel R K H S)
    (hS : S.Finite) : Continuous (M.toRestrictedProductMonoidHom hS) := by
  rw [continuous_iff_continuousAt]; intro x₀
  obtain ⟨T, hST, hT, hx₀⟩ := M.exists_finite_mem_sIntegralAdelicPoints hS x₀
  have hrestr : Continuous ((M.sIntegralAdelicPoints T hST : Set _).domRestrict
      (M.toRestrictedProductMonoidHom hS)) :=
    (continuous_restrictedProduct_iff_of_forall_mem (T := Tᶜ)
      (le_principal_iff.mpr hT.compl_mem_cofinite) fun u v hv ↦ by
        rw [SetLike.mem_coe, M.level_of_notMem (fun hvS ↦ hv (hST hvS))]
        exact (M.mem_sIntegralAdelicPoints_iff_forall_localPoints hST).mp u.2 v hv).mpr <|
      continuous_pi fun v ↦
        (FiniteAdelicPoints.continuous_localProjection v).comp continuous_subtype_val
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestr).continuousAt
    ((M.isOpen_sIntegralAdelicPoints T hST).mem_nhds hx₀)

private noncomputable def evalRestrictedProductAdele (M : IntegralModel R K H S) (hS : S.Finite)
    (h : H) : RestrictedProductGroup M.level → FiniteAdeleRing R K :=
  RestrictedProduct.mapAlong (fun v ↦ LocalPoints K H v) (fun v ↦ v.adicCompletion K)
    (A₁ := fun v ↦ (M.level v : Set (LocalPoints K H v)))
    (A₂ := fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    id tendsto_id (fun _ g ↦ g.ofConv h) (M.eventually_level_ofConv_mem hS h)

private noncomputable def ofRestrictedProduct (M : IntegralModel R K H S) (hS : S.Finite)
    (y : RestrictedProductGroup M.level) : FiniteAdelicPoints R K H :=
  toConv
    { toFun := fun h ↦ M.evalRestrictedProductAdele hS h y
      map_one' := FiniteAdeleRing.ext K fun v ↦ map_one (y v).ofConv
      map_mul' := fun a b ↦ FiniteAdeleRing.ext K fun v ↦ map_mul (y v).ofConv a b
      map_zero' := FiniteAdeleRing.ext K fun v ↦ map_zero (y v).ofConv
      map_add' := fun a b ↦ FiniteAdeleRing.ext K fun v ↦ map_add (y v).ofConv a b
      commutes' := fun k ↦ FiniteAdeleRing.ext K fun v ↦ by
        change (y v).ofConv (algebraMap K H k) = algebraMap K (FiniteAdeleRing R K) k v
        rw [(y v).ofConv.commutes, FiniteAdeleRing.algebraMap_apply]
        exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion R K v (S := K)) k }

/-- Restricted-product presentation `G(𝔸ᶠ[R, K]) ≃ₜ* RestrictedProductGroup M.level` for finite
`S` (Conrad 2012, Theorem 3.4). -/
noncomputable def finiteAdelicPointsContinuousMulEquiv (M : IntegralModel R K H S)
    (hS : S.Finite) : FiniteAdelicPoints R K H ≃ₜ* RestrictedProductGroup M.level where
  toFun := M.toRestrictedProductMonoidHom hS
  invFun := M.ofRestrictedProduct hS
  left_inv x := WithConv.ofConv_injective <| AlgHom.ext fun h ↦ FiniteAdeleRing.ext K fun v ↦
    FiniteAdelicPoints.localProjection_apply_ofConv v x h
  right_inv y := DFunLike.ext _ _ fun v ↦ WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    FiniteAdelicPoints.localProjection_apply_ofConv v (M.ofRestrictedProduct hS y) h
  map_mul' := (M.toRestrictedProductMonoidHom hS).map_mul'
  continuous_toFun := M.continuous_toRestrictedProductMonoidHom hS
  continuous_invFun := continuous_withConv_iff.mpr fun h ↦
    (RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ _
      (fun _ ↦ continuous_eval_ofConv h) : Continuous (M.evalRestrictedProductAdele hS h))

/-- At `v`, `M.finiteAdelicPointsContinuousMulEquiv hS x v = localProjection R K H v x`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (x : FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS x v = FiniteAdelicPoints.localProjection R K H v x :=
  (rfl)

/-- Evaluating `M.finiteAdelicPointsContinuousMulEquiv hS x v` on `h` gives `x.ofConv h v`. -/
theorem finiteAdelicPointsContinuousMulEquiv_apply_ofConv (M : IntegralModel R K H S)
    (hS : S.Finite) (x : FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) (h : H) :
    (M.finiteAdelicPointsContinuousMulEquiv hS x v).ofConv h = x.ofConv h v :=
  FiniteAdelicPoints.localProjection_apply_ofConv v x h

/-- Evaluating `(M.finiteAdelicPointsContinuousMulEquiv hS).symm y` at `h` and `v`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    (hS : S.Finite) (y : RestrictedProductGroup M.level) (h : H) (v : HeightOneSpectrum R) :
    ((M.finiteAdelicPointsContinuousMulEquiv hS).symm y).ofConv h v = (y v).ofConv h := (rfl)

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` sends `diagonal` to `LocalPoints.diagonal`. -/
theorem finiteAdelicPointsContinuousMulEquiv_diagonal (M : IntegralModel R K H S) (hS : S.Finite)
    (g : WithConv (H →ₐ[K] K)) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS (FiniteAdelicPoints.diagonal R K H g) v =
      LocalPoints.diagonal K H v g := by simp

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` maps `M.sIntegralAdelicPoints S Set.Subset.rfl`
onto `integralSubgroup M.level`. -/
@[simp]
theorem map_sIntegralAdelicPoints_self (M : IntegralModel R K H S) (hS : S.Finite) :
    (M.sIntegralAdelicPoints S Set.Subset.rfl).map
        ((M.finiteAdelicPointsContinuousMulEquiv hS :
          FiniteAdelicPoints R K H ≃* RestrictedProductGroup M.level) :
          FiniteAdelicPoints R K H →* RestrictedProductGroup M.level) =
      integralSubgroup M.level := by
  ext y; rw [Subgroup.mem_map, mem_integralSubgroup]
  refine ⟨?_, fun hy ↦ ⟨(M.finiteAdelicPointsContinuousMulEquiv hS).symm y, ?_,
    (M.finiteAdelicPointsContinuousMulEquiv hS).apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩ v; by_cases hv : v ∈ S
    · simp [hv]
    · rw [M.level_of_notMem hv]
      exact (M.mem_sIntegralAdelicPoints_iff_forall_localPoints Set.Subset.rfl).mp hx v hv
  · rw [M.mem_sIntegralAdelicPoints_iff_forall_localPoints Set.Subset.rfl]; intro v hv
    have hv' := hy v; rw [M.level_of_notMem hv] at hv'
    simpa [show FiniteAdelicPoints.localProjection R K H v
      ((M.finiteAdelicPointsContinuousMulEquiv hS).symm y) = y v from by ext h; simp] using hv'

/-- Restricted-product presentation `G(𝔸[R, K]) ≃ₜ* G(K_∞) × Πʳ v, [G(K_v), M.level v]`
(Conrad 2012, Theorem 3.6). -/
noncomputable def adelicPointsContinuousMulEquiv (M : IntegralModel R K H S) (hS : S.Finite) :
    AdelicPoints R K H ≃ₜ* RestrictedProductGroupWithFactor (InfinitePoints K H) M.level :=
  (AdelicPoints.splittingContinuousMulEquiv R K H).trans
    { (MulEquiv.refl (InfinitePoints K H)).prodCongr
        (M.finiteAdelicPointsContinuousMulEquiv hS).toMulEquiv with
      continuous_toFun := continuous_fst.prodMk
        ((M.finiteAdelicPointsContinuousMulEquiv hS).continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk
        ((M.finiteAdelicPointsContinuousMulEquiv hS).symm.continuous.comp continuous_snd) }

/-- Archimedean component of `M.adelicPointsContinuousMulEquiv hS x`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_fst (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints R K H) :
    (M.adelicPointsContinuousMulEquiv hS x).1 = AdelicPoints.infiniteProjection R K H x :=
  AdelicPoints.splittingContinuousMulEquiv_fst x

/-- Finite-place restricted-product component of `M.adelicPointsContinuousMulEquiv hS x`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_snd (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints R K H) :
    (M.adelicPointsContinuousMulEquiv hS x).2 =
      M.finiteAdelicPointsContinuousMulEquiv hS (AdelicPoints.finiteProjection R K H x) :=
  congrArg (M.finiteAdelicPointsContinuousMulEquiv hS)
    (AdelicPoints.splittingContinuousMulEquiv_snd x)

/-- Inverse of `M.adelicPointsContinuousMulEquiv hS`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_symm_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (p : RestrictedProductGroupWithFactor (InfinitePoints K H) M.level) :
    (M.adelicPointsContinuousMulEquiv hS).symm p = (AdelicPoints.splittingContinuousMulEquiv
      R K H).symm (p.1, (M.finiteAdelicPointsContinuousMulEquiv hS).symm p.2) := (rfl)

/-- Model independence via `restrictedProductCongr` (Conrad 2012, Prop. 3.3, Thm. 3.4). -/
@[simp]
theorem restrictedProductCongr_finiteAdelicPointsContinuousMulEquiv
    {S₁ S₂ : Set (HeightOneSpectrum R)} (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) (x : FiniteAdelicPoints R K H) :
    restrictedProductCongr M₁.level M₂.level (level_eventuallyEq M₁ M₂ hS₁ hS₂)
        (M₁.finiteAdelicPointsContinuousMulEquiv hS₁ x) =
      M₂.finiteAdelicPointsContinuousMulEquiv hS₂ x :=
  DFunLike.ext _ _ fun v ↦ by simp

end TauCeti.IntegralModel
