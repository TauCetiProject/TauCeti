/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.IntegralModel
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng

/-!
# Restricted-product presentation of finite-adelic and `𝔸[R, K]`-valued points

For `M : IntegralModel R K H S` with `S.Finite`, this file proves the Weil–Grothendieck
restricted-product comparison (Conrad 2012, Theorems 3.4 and 3.6):
* `M.finiteAdelicPointsContinuousMulEquiv hS : AdelicPoints.FiniteAdelicPoints R K H ≃ₜ*
  RestrictedProductGroup M.level`, mapping `M.sIntegralAdelicPoints T hST` onto
  `integralSubgroupOf M.level (fun v ↦ if v ∈ T then ⊤ else M.level v)` (and in particular
  `M.sIntegralAdelicPoints S Set.Subset.rfl` onto `integralSubgroup M.level`);
* `M.adelicPointsContinuousMulEquiv hS : AdelicPoints R K H ≃ₜ*
  RestrictedProductGroupWithFactor (AdelicPoints.InfinitePoints K H) M.level`;
* `restrictedProductCongr_finiteAdelicPointsContinuousMulEquiv`: model independence.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 3.3, Thm. 3.4, and Thm. 3.6.
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

/-- For `T ⊇ S`, `M.sIntegralAdelicPoints T hST` is the subgroup of
`AdelicPoints.FiniteAdelicPoints R K H` arising from
`(FiniteAdeleRing.sIntegralAdeles R K T)`-valued points of `M.coordinate`. -/
noncomputable def sIntegralAdelicPoints (M : IntegralModel R K H S)
    (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) :
    Subgroup (AdelicPoints.FiniteAdelicPoints R K H) :=
  M.subalgebraPoints (FiniteAdeleRing.sIntegralAdelesSubalgebra R K S T hST)

/-- `x ∈ M.sIntegralAdelicPoints T hST` iff `x` maps `M.toGenericFiber` into
`FiniteAdeleRing.sIntegralAdeles`. -/
@[simp]
theorem mem_sIntegralAdelicPoints_iff (M : IntegralModel R K H S) {T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) {x : AdelicPoints.FiniteAdelicPoints R K H} :
    x ∈ M.sIntegralAdelicPoints T hST ↔
      ∀ m : M.coordinate,
        x.ofConv (M.toGenericFiber m) ∈ FiniteAdeleRing.sIntegralAdeles R K T := by
  rw [sIntegralAdelicPoints]
  simpa only [FiniteAdeleRing.mem_sIntegralAdelesSubalgebra] using
    M.mem_subalgebraPoints_iff (FiniteAdeleRing.sIntegralAdelesSubalgebra R K S T hST)

/-- `x ∈ M.sIntegralAdelicPoints T hST` iff its projection at every `v ∉ T` lies in
`M.localPoints`. -/
theorem mem_sIntegralAdelicPoints_iff_forall_localPoints (M : IntegralModel R K H S)
    {T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) {x : AdelicPoints.FiniteAdelicPoints R K H} :
    x ∈ M.sIntegralAdelicPoints T hST ↔ ∀ (v : HeightOneSpectrum R) (hv : v ∉ T),
      AdelicPoints.finiteLocalProjection R K H v x ∈ M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_sIntegralAdelicPoints_iff, FiniteAdeleRing.mem_sIntegralAdeles,
    mem_localPoints_iff]
  have hproj (v : HeightOneSpectrum R) (m : M.coordinate) :
      (AdelicPoints.finiteLocalProjection R K H v x).ofConv (M.toGenericFiber m) =
        x.ofConv (M.toGenericFiber m) v :=
    AdelicPoints.finiteLocalProjection_apply_apply v x (M.toGenericFiber m)
  simp only [hproj]
  exact ⟨fun h v hv m ↦ h m v hv, fun h m v hv ↦ h v hv m⟩

/-- Every `M.sIntegralAdelicPoints T hST` is open in `AdelicPoints.FiniteAdelicPoints R K H`. -/
theorem isOpen_sIntegralAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) :
    IsOpen (M.sIntegralAdelicPoints T hST : Set (AdelicPoints.FiniteAdelicPoints R K H)) :=
  M.isOpen_subalgebraPoints (FiniteAdeleRing.sIntegralAdelesSubalgebra R K S T hST)
    (by rw [FiniteAdeleRing.coe_sIntegralAdelesSubalgebra]
        exact FiniteAdeleRing.isOpen_sIntegralAdeles R K T)

/-- Every `M.sIntegralAdelicPoints T hST` is closed in `AdelicPoints.FiniteAdelicPoints R K H`. -/
theorem isClosed_sIntegralAdelicPoints (M : IntegralModel R K H S) (T : Set (HeightOneSpectrum R))
    (hST : S ⊆ T) :
    IsClosed (M.sIntegralAdelicPoints T hST : Set (AdelicPoints.FiniteAdelicPoints R K H)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_sIntegralAdelicPoints T hST)

/-- For `S = ∅` and finite residue fields, `M.sIntegralAdelicPoints ∅ Set.Subset.rfl` is
compact. -/
theorem isCompact_sIntegralAdelicPoints_empty
    (M : IntegralModel R K H (∅ : Set (HeightOneSpectrum R)))
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    IsCompact
      (M.sIntegralAdelicPoints ∅ Set.Subset.rfl : Set (AdelicPoints.FiniteAdelicPoints R K H)) := by
  have hset :
      (FiniteAdeleRing.sIntegralAdelesSubalgebra R K ∅ ∅ Set.Subset.rfl :
        Set (FiniteAdeleRing R K)) =
        FiniteAdeleRing.sIntegralAdeles R K ∅ :=
    FiniteAdeleRing.coe_sIntegralAdelesSubalgebra (R := R) (K := K) ∅ ∅ Set.Subset.rfl
  let _ : CompactSpace (FiniteAdeleRing.sIntegralAdelesSubalgebra R K ∅ ∅ Set.Subset.rfl) :=
    isCompact_iff_compactSpace.mp <| by
      rw [hset, FiniteAdeleRing.sIntegralAdeles_empty]
      exact FiniteAdeleRing.isCompact_integralAdeles
  exact M.isCompact_subalgebraPoints _

/-- Enlarging `S` to `S'` preserves `sIntegralAdelicPoints T` for every `T ⊇ S'`. -/
@[simp]
theorem sIntegralAdelicPoints_enlarge {S' : Set (HeightOneSpectrum R)} (M : IntegralModel R K H S)
    (hSS' : S ⊆ S') (T : Set (HeightOneSpectrum R)) (hS'T : S' ⊆ T) :
    (M.enlarge hSS').sIntegralAdelicPoints T hS'T =
      M.sIntegralAdelicPoints T (hSS'.trans hS'T) :=
  M.subalgebraPoints_enlarge hSS' _ _ (by simp)

/-- Enlarging `T` enlarges `M.sIntegralAdelicPoints`. -/
theorem sIntegralAdelicPoints_mono (M : IntegralModel R K H S) {T₁ T₂ : Set (HeightOneSpectrum R)}
    (hST₁ : S ⊆ T₁) (hT₁₂ : T₁ ⊆ T₂) :
    M.sIntegralAdelicPoints T₁ hST₁ ≤ M.sIntegralAdelicPoints T₂ (hST₁.trans hT₁₂) := fun _ hx ↦
  (mem_sIntegralAdelicPoints_iff M _).mpr fun m ↦
    FiniteAdeleRing.sIntegralAdeles_mono R K hT₁₂ ((mem_sIntegralAdelicPoints_iff M _).mp hx m)

/-- Pulling back `M.sIntegralAdelicPoints T hST` along `finiteDiagonal` recovers
`M.globalPoints T`. -/
@[simp]
theorem comap_finiteDiagonal_sIntegralAdelicPoints (M : IntegralModel R K H S)
    (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) :
    (M.sIntegralAdelicPoints T hST).comap (AdelicPoints.finiteDiagonal R K H) =
      M.globalPoints T hST := by
  ext g
  simp only [Subgroup.mem_comap, mem_sIntegralAdelicPoints_iff, mem_globalPoints_iff]
  refine forall_congr' fun m ↦ ?_
  have hdiag : (AdelicPoints.finiteDiagonal R K H g).ofConv (M.toGenericFiber m) =
      algebraMap K (FiniteAdeleRing R K) (g.ofConv (M.toGenericFiber m)) :=
    AdelicPoints.finiteDiagonal_apply_apply g (M.toGenericFiber m)
  simp only [hdiag, FiniteAdeleRing.algebraMap_mem_sIntegralAdeles_iff]

/-- Exhaustion of `G(𝔸ᶠ[R, K])` by open `T`-integral subgroups for finite `T ⊇ S` when `S` is
finite. -/
theorem exists_finite_mem_sIntegralAdelicPoints (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints.FiniteAdelicPoints R K H) :
    ∃ (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T),
      T.Finite ∧ x ∈ M.sIntegralAdelicPoints T hST := by
  obtain ⟨F, hgen⟩ := M.exists_finset_adjoin_eq_top
  choose U hU using fun i : F ↦
    FiniteAdeleRing.exists_finset_mem_sIntegralAdeles (x.ofConv (M.toGenericFiber i))
  refine ⟨S ∪ ⋃ i : F, (U i : Set (HeightOneSpectrum R)), Set.subset_union_left,
    hS.union (Set.finite_iUnion fun i ↦ (U i).finite_toSet), ?_⟩
  rw [sIntegralAdelicPoints, M.mem_subalgebraPoints_iff_of_adjoin_eq_top _ hgen]
  exact fun i ↦ (FiniteAdeleRing.mem_sIntegralAdelesSubalgebra ..).mpr
    (FiniteAdeleRing.sIntegralAdeles_mono R K
      ((Set.subset_iUnion (fun j : F ↦ (U j : Set (HeightOneSpectrum R))) i).trans
        Set.subset_union_right) (hU i))

/-- When `S` is finite, `⨆_{T ⊇ S finite} M.sIntegralAdelicPoints T = ⊤`. -/
theorem iSup_sIntegralAdelicPoints_eq_top (M : IntegralModel R K H S) (hS : S.Finite) :
    (⨆ T : {T : Set (HeightOneSpectrum R) // S ⊆ T ∧ T.Finite},
      M.sIntegralAdelicPoints T.val T.property.left) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ let ⟨T, hST, hT, hx⟩ := M.exists_finite_mem_sIntegralAdelicPoints hS x
    Subgroup.mem_iSup_of_mem ⟨T, hST, hT⟩ hx

/-- For any model `M`, `finiteLocalProjection v x ∈ M.level v` at all but finitely many places
`v`. -/
theorem eventually_finiteLocalProjection_mem_level (M : IntegralModel R K H S)
    (x : AdelicPoints.FiniteAdelicPoints R K H) :
    ∀ᶠ v in cofinite, AdelicPoints.finiteLocalProjection R K H v x ∈ M.level v := by
  obtain ⟨F, hgen⟩ := M.exists_finset_adjoin_eq_top
  filter_upwards [eventually_all.mpr fun i : F ↦
    (x.ofConv (M.toGenericFiber i)).property] with v hv
  by_cases hvS : v ∈ S
  · rw [M.level_of_mem hvS]; exact Subgroup.mem_top _
  · rw [M.level_of_notMem hvS, M.mem_localPoints_iff_of_adjoin_eq_top hvS hgen]
    exact fun i ↦ (AdelicPoints.finiteLocalProjection_apply_apply v x (M.toGenericFiber i)) ▸ hv i

private noncomputable def toRestrictedProductMonoidHom (M : IntegralModel R K H S) :
    AdelicPoints.FiniteAdelicPoints R K H →* RestrictedProductGroup M.level where
  toFun x := ⟨fun v ↦ AdelicPoints.finiteLocalProjection R K H v x,
    M.eventually_finiteLocalProjection_mem_level x⟩
  map_one' := DFunLike.ext _ _ fun v ↦ map_one (AdelicPoints.finiteLocalProjection R K H v)
  map_mul' x y :=
    DFunLike.ext _ _ fun v ↦ map_mul (AdelicPoints.finiteLocalProjection R K H v) x y

private theorem toRestrictedProductMonoidHom_apply (M : IntegralModel R K H S)
    (x : AdelicPoints.FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) :
    M.toRestrictedProductMonoidHom x v = AdelicPoints.finiteLocalProjection R K H v x := (rfl)

private theorem continuous_toRestrictedProductMonoidHom (M : IntegralModel R K H S)
    (hS : S.Finite) : Continuous M.toRestrictedProductMonoidHom := by
  rw [continuous_iff_continuousAt]; intro x₀
  obtain ⟨T, hST, hT, hx₀⟩ := M.exists_finite_mem_sIntegralAdelicPoints hS x₀
  have hrestr : Continuous ((M.sIntegralAdelicPoints T hST : Set _).domRestrict
      M.toRestrictedProductMonoidHom) :=
    (continuous_restrictedProduct_iff_of_forall_mem (T := Tᶜ)
      (le_principal_iff.mpr hT.compl_mem_cofinite) fun u v hv ↦ by
        simp only [SetLike.mem_coe, Set.domRestrict_apply,
          M.level_of_notMem (fun hvS ↦ hv (hST hvS)), toRestrictedProductMonoidHom_apply]
        exact (M.mem_sIntegralAdelicPoints_iff_forall_localPoints hST).mp u.property v hv).mpr <|
      continuous_pi fun v ↦
        (AdelicPoints.continuous_finiteLocalProjection v).comp continuous_subtypeVal
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestr).continuousAt
    ((M.isOpen_sIntegralAdelicPoints T hST).mem_nhds hx₀)

private noncomputable def evalRestrictedProductAdele (M : IntegralModel R K H S) (hS : S.Finite)
    (h : H) : RestrictedProductGroup M.level → FiniteAdeleRing R K :=
  RestrictedProduct.mapAlong (fun v ↦ AdelicPoints.LocalPoints R K H v)
    (fun v ↦ v.adicCompletion K)
    (A₁ := fun v ↦ (M.level v : Set (AdelicPoints.LocalPoints R K H v)))
    (A₂ := fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    id tendsto_id (fun _ g ↦ g.ofConv h) (M.eventually_level_ofConv_mem hS h)

private theorem evalRestrictedProductAdele_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (h : H) (y : RestrictedProductGroup M.level) (v : HeightOneSpectrum R) :
    M.evalRestrictedProductAdele hS h y v = (y v).ofConv h := (rfl)

private noncomputable def ofRestrictedProduct (M : IntegralModel R K H S) (hS : S.Finite)
    (y : RestrictedProductGroup M.level) : AdelicPoints.FiniteAdelicPoints R K H :=
  toConv
    { toFun := fun h ↦ M.evalRestrictedProductAdele hS h y
      map_one' := FiniteAdeleRing.ext K fun v ↦ by simp [evalRestrictedProductAdele_apply]
      map_mul' := fun a b ↦
        FiniteAdeleRing.ext K fun v ↦ by simp [evalRestrictedProductAdele_apply]
      map_zero' := FiniteAdeleRing.ext K fun v ↦ by simp [evalRestrictedProductAdele_apply]
      map_add' := fun a b ↦
        FiniteAdeleRing.ext K fun v ↦ by simp [evalRestrictedProductAdele_apply]
      commutes' := fun k ↦ FiniteAdeleRing.ext K fun v ↦ by
        rw [evalRestrictedProductAdele_apply, (y v).ofConv.commutes,
          FiniteAdeleRing.algebraMap_apply]
        exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion R K v (S := K)) k }

private theorem ofRestrictedProduct_apply_ofConv (M : IntegralModel R K H S) (hS : S.Finite)
    (y : RestrictedProductGroup M.level) (h : H) (v : HeightOneSpectrum R) :
    (M.ofRestrictedProduct hS y).ofConv h v = (y v).ofConv h := (rfl)

/-- Restricted-product presentation `G(𝔸ᶠ[R, K]) ≃ₜ* RestrictedProductGroup M.level` for finite
`S` (Conrad 2012, Theorem 3.4). -/
noncomputable def finiteAdelicPointsContinuousMulEquiv (M : IntegralModel R K H S)
    (hS : S.Finite) :
    AdelicPoints.FiniteAdelicPoints R K H ≃ₜ* RestrictedProductGroup M.level where
  toFun := M.toRestrictedProductMonoidHom
  invFun := M.ofRestrictedProduct hS
  left_inv x := WithConv.ofConv_injective <| AlgHom.ext fun h ↦ FiniteAdeleRing.ext K fun v ↦ by
    rw [ofRestrictedProduct_apply_ofConv, toRestrictedProductMonoidHom_apply,
      AdelicPoints.finiteLocalProjection_apply_apply]
  right_inv y := DFunLike.ext _ _ fun v ↦ WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by
    rw [toRestrictedProductMonoidHom_apply, AdelicPoints.finiteLocalProjection_apply_apply,
      ofRestrictedProduct_apply_ofConv]
  map_mul' := M.toRestrictedProductMonoidHom.map_mul'
  continuous_toFun := M.continuous_toRestrictedProductMonoidHom hS
  continuous_invFun := continuous_withConv_iff.mpr fun h ↦
    (RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ _
      (fun _ ↦ continuous_eval_ofConv h) :
        Continuous (M.evalRestrictedProductAdele hS h))

/-- At `v`, `M.finiteAdelicPointsContinuousMulEquiv hS x v = finiteLocalProjection R K H v x`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints.FiniteAdelicPoints R K H) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS x v =
      AdelicPoints.finiteLocalProjection R K H v x :=
  (rfl)

/-- Evaluating `(M.finiteAdelicPointsContinuousMulEquiv hS).symm y` at `h` and `v`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_symm_apply_ofConv (M : IntegralModel R K H S)
    (hS : S.Finite) (y : RestrictedProductGroup M.level) (h : H) (v : HeightOneSpectrum R) :
    ((M.finiteAdelicPointsContinuousMulEquiv hS).symm y).ofConv h v = (y v).ofConv h :=
  (rfl)

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` sends `finiteDiagonal` to the local `v`-adic
image of `g` at each place `v`. -/
theorem finiteAdelicPointsContinuousMulEquiv_finiteDiagonal (M : IntegralModel R K H S)
    (hS : S.Finite) (g : WithConv (H →ₐ[K] K)) (v : HeightOneSpectrum R) :
    M.finiteAdelicPointsContinuousMulEquiv hS (AdelicPoints.finiteDiagonal R K H g) v =
      AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K)) g := by
  rw [finiteAdelicPointsContinuousMulEquiv_apply, AdelicPoints.finiteLocalProjection_finiteDiagonal]

open scoped Classical in
/-- `M.finiteAdelicPointsContinuousMulEquiv hS` maps `M.sIntegralAdelicPoints T hST` onto the
subgroup of `RestrictedProductGroup M.level` whose `v`-coordinate is unrestricted on `T` and lies
in `M.level v` outside `T`. -/
theorem map_sIntegralAdelicPoints (M : IntegralModel R K H S) (hS : S.Finite)
    (T : Set (HeightOneSpectrum R)) (hST : S ⊆ T) :
    (M.sIntegralAdelicPoints T hST).map
        ((M.finiteAdelicPointsContinuousMulEquiv hS :
          AdelicPoints.FiniteAdelicPoints R K H ≃* RestrictedProductGroup M.level) :
          AdelicPoints.FiniteAdelicPoints R K H →* RestrictedProductGroup M.level) =
      integralSubgroupOf M.level (fun v ↦ if v ∈ T then ⊤ else M.level v) := by
  ext y
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, mem_integralSubgroupOf,
    M.mem_sIntegralAdelicPoints_iff_forall_localPoints hST]
  have hy (v : HeightOneSpectrum R) :
      AdelicPoints.finiteLocalProjection R K H v
        ((M.finiteAdelicPointsContinuousMulEquiv hS :
          AdelicPoints.FiniteAdelicPoints R K H ≃* RestrictedProductGroup M.level).symm y) =
        y v :=
    congrArg (· v) ((M.finiteAdelicPointsContinuousMulEquiv hS).apply_symm_apply y)
  simp only [hy]
  refine ⟨fun h v ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hv : v ∈ T
    · simp [hv]
    · simp [hv, M.level_of_notMem (fun hvS ↦ hv (hST hvS)), h v hv]
  · simpa [hv, M.level_of_notMem (fun hvS ↦ hv (hST hvS))] using h v

/-- `M.finiteAdelicPointsContinuousMulEquiv hS` maps `M.sIntegralAdelicPoints S Set.Subset.rfl`
onto `integralSubgroup M.level`. -/
@[simp]
theorem map_sIntegralAdelicPoints_self (M : IntegralModel R K H S) (hS : S.Finite) :
    (M.sIntegralAdelicPoints S Set.Subset.rfl).map
        ((M.finiteAdelicPointsContinuousMulEquiv hS :
          AdelicPoints.FiniteAdelicPoints R K H ≃* RestrictedProductGroup M.level) :
          AdelicPoints.FiniteAdelicPoints R K H →* RestrictedProductGroup M.level) =
      integralSubgroup M.level := by
  classical
  rw [M.map_sIntegralAdelicPoints hS S Set.Subset.rfl, ← integralSubgroupOf_self]
  congr 1; funext v; split_ifs with hv <;> simp [hv]

/-- Restricted-product presentation `G(𝔸[R, K]) ≃ₜ* G(K_∞) × Πʳ v, [G(K_v), M.level v]`
(Conrad 2012, Theorem 3.6). -/
noncomputable def adelicPointsContinuousMulEquiv (M : IntegralModel R K H S) (hS : S.Finite) :
    AdelicPoints R K H ≃ₜ*
      RestrictedProductGroupWithFactor (AdelicPoints.InfinitePoints K H) M.level :=
  (AdelicPoints.prodContinuousMulEquiv R K H).trans
    { (MulEquiv.refl (AdelicPoints.InfinitePoints K H)).prodCongr
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
  congrArg Prod.fst (AdelicPoints.prodContinuousMulEquiv_apply x)

/-- Finite-place restricted-product component of `M.adelicPointsContinuousMulEquiv hS x`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_snd (M : IntegralModel R K H S) (hS : S.Finite)
    (x : AdelicPoints R K H) :
    (M.adelicPointsContinuousMulEquiv hS x).2 =
      M.finiteAdelicPointsContinuousMulEquiv hS (AdelicPoints.finiteProjection R K H x) :=
  congrArg (M.finiteAdelicPointsContinuousMulEquiv hS)
    (congrArg Prod.snd (AdelicPoints.prodContinuousMulEquiv_apply x))

/-- Inverse of `M.adelicPointsContinuousMulEquiv hS`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_symm_apply (M : IntegralModel R K H S) (hS : S.Finite)
    (p : RestrictedProductGroupWithFactor (AdelicPoints.InfinitePoints K H) M.level) :
    (M.adelicPointsContinuousMulEquiv hS).symm p = (AdelicPoints.prodContinuousMulEquiv
      R K H).symm (p.1, (M.finiteAdelicPointsContinuousMulEquiv hS).symm p.2) := (rfl)

/-- Model independence via `restrictedProductCongr` (Conrad 2012, Prop. 3.3, Thm. 3.4). -/
@[simp]
theorem restrictedProductCongr_finiteAdelicPointsContinuousMulEquiv
    {S₁ S₂ : Set (HeightOneSpectrum R)} (M₁ : IntegralModel R K H S₁) (M₂ : IntegralModel R K H S₂)
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) (x : AdelicPoints.FiniteAdelicPoints R K H) :
    restrictedProductCongr M₁.level M₂.level (level_eventuallyEq M₁ M₂ hS₁ hS₂)
        (M₁.finiteAdelicPointsContinuousMulEquiv hS₁ x) =
      M₂.finiteAdelicPointsContinuousMulEquiv hS₂ x :=
  DFunLike.ext _ _ fun v ↦ by simp

end TauCeti.IntegralModel
