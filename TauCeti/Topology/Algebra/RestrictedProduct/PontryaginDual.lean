/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.CharacterFactorization
public import TauCeti.Topology.Algebra.RestrictedProduct.Box
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
import TauCeti.Topology.Algebra.RestrictedProduct.ProductLevel

/-!
# Duality of restricted products

Let `G i` be topological groups with open subgroups `B i`, compact for all but finitely many `i`.
Restriction of characters to the factors is a topological isomorphism
`PontryaginDual.restrictedProductContinuousMulEquiv` from the Pontryagin dual of
`Πʳ i, [G i, B i]` onto `Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]`, where the
dual carries the compact-open topology and the target the restricted-product topology. The
underlying group isomorphism is `PontryaginDual.restrictedProductMulEquiv`.

## Main results

* `PontryaginDual.isOpen_setOfPred_mapsTo`: the characters mapping a compact set into an open
  subset of the circle form an open set of the dual.
* `Subgroup.isOpen_pontryaginAnnihilator`: the annihilator of a compact subgroup is open.
* `PontryaginDual.continuous_restrictedProductMulEquiv`: restriction to the factors is
  continuous when cofinitely many `B i` are compact; openness of the `B i` is not needed.
* `PontryaginDual.continuous_restrictedProductMulEquiv_symm`: the inverse, assembling local
  characters by a finite product, is continuous when every `B i` is open and cofinitely many are
  compact.
* `PontryaginDual.restrictedProductContinuousMulEquiv`: the resulting isomorphism of topological
  groups.

## Implementation notes

No local compactness, commutativity or Hausdorff assumption is made on the factors. Forward
continuity uses that, for a set `T` of indices on which `B i` is compact, the characters trivial
on `B i` for every `i ∈ T` are those mapping the compact box `∏_(i∈T) B i × ∏_(i∉T) {1}` into the
half circle `Circle.centeredArc (π / 2)`, which contains no nontrivial subgroup. Convergence in
the restricted product is then coordinatewise. For the inverse, a compact subset of the
restricted product has all coordinates in `B i` outside a finite set `S`, so on it the
assembled character is a product over `S`, and the compact-open neighbourhoods are controlled
factor by factor.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), §3.2.
* AnalyticNumberTheoryPartII roadmap, §5.3h.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace PontryaginDual

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- The characters mapping a compact set into an open subset of the circle form an open subset
of the Pontryagin dual. This is a subbasic open set of the compact-open topology. -/
theorem isOpen_setOfPred_mapsTo {K : Set G} (hK : IsCompact K) {U : Set Circle}
    (hU : IsOpen U) : IsOpen {χ : PontryaginDual G | MapsTo χ K U} :=
  (ContinuousMap.isOpen_setOfPred_mapsTo hK hU).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous

/-- Characters close enough to the trivial character map a given compact set into a given
neighbourhood of `1` in the circle. -/
theorem eventually_mapsTo_one {K : Set G} (hK : IsCompact K) {V : Set Circle}
    (hV : V ∈ 𝓝 1) : ∀ᶠ χ : PontryaginDual G in 𝓝 1, MapsTo χ K V := by
  obtain ⟨W, hWV, hWo, hW1⟩ := mem_nhds_iff.mp hV
  filter_upwards [(isOpen_setOfPred_mapsTo hK hWo).mem_nhds fun _ _ ↦ hW1] with χ hχ
  exact hχ.mono_right hWV

end PontryaginDual

namespace Circle

/-- The half circle `Circle.centeredArc (π / 2)` contains `1`. -/
theorem one_mem_centeredArc_pi_div_two : (1 : Circle) ∈ centeredArc (Real.pi / 2) :=
  ⟨0, by simp [Real.pi_pos], Circle.exp_zero⟩

end Circle

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A character is trivial on a subgroup exactly when it maps the subgroup into the half
circle, since that arc contains no nontrivial subgroup of the circle. -/
theorem coe_pontryaginAnnihilator_eq_setOf_mapsTo (H : Subgroup G) :
    (H.pontryaginAnnihilator : Set (PontryaginDual G)) =
      {χ : PontryaginDual G | MapsTo χ (H : Set G) (Circle.centeredArc (Real.pi / 2))} := by
  ext χ
  simp only [SetLike.mem_coe, mem_pontryaginAnnihilator, mem_ofPred_eq]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · rw [h x hx]
    exact Circle.one_mem_centeredArc_pi_div_two
  · refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
    rw [← map_pow]
    exact h (H.pow_mem hx n)

/-- The annihilator of a compact subgroup is open in the Pontryagin dual. -/
theorem isOpen_pontryaginAnnihilator {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsOpen (H.pontryaginAnnihilator : Set (PontryaginDual G)) := by
  rw [coe_pontryaginAnnihilator_eq_setOf_mapsTo]
  exact PontryaginDual.isOpen_setOfPred_mapsTo hH (Circle.isOpen_centeredArc _)

end Subgroup

namespace PontryaginDual

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (B : ∀ i, Subgroup (G i))

/-- If every coordinate of `x` lies in `B i` outside a finite set `S` and every local character
`ψ i` is trivial on `B i` outside `S`, the assembled character takes at `x` the finite product of
the local values over `S`. -/
theorem restrictedProductMulEquiv_symm_apply_eq_prod {S : Finset ι}
    {ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]}
    (hψ : ∀ i ∉ S, ψ i ∈ (B i).pontryaginAnnihilator) {x : Πʳ i, [G i, B i]}
    (hx : ∀ i ∉ S, x i ∈ B i) :
    (restrictedProductMulEquiv B).symm ψ x = ∏ i ∈ S, ψ i (x i) := by
  rw [restrictedProductMulEquiv_symm_apply_apply]
  refine finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ ?_
  by_contra hiS
  exact hi (Subgroup.mem_pontryaginAnnihilator.mp (hψ i hiS) _ (hx i hiS))

/-- For any set `T` of indices, the characters of the restricted product whose restriction to
`G i` is trivial on `B i` for every `i ∈ T` are exactly those mapping the box
`∏_(i∈T) B i × ∏_(i∉T) {1}` into the half circle. -/
theorem setOf_forall_restrictMulSingle_mem_eq_setOf_mapsTo (T : Set ι)
    [DecidablePred (· ∈ T)] :
    {χ : PontryaginDual (Πʳ i, [G i, B i]) |
        ∀ i ∈ T, restrictMulSingle B i χ ∈ (B i).pontryaginAnnihilator} =
      {χ : PontryaginDual (Πʳ i, [G i, B i]) |
        MapsTo χ (RestrictedProduct.box fun i ↦ if i ∈ T then (B i : Set (G i)) else {1})
          (Circle.centeredArc (Real.pi / 2))} := by
  classical
  ext χ
  simp only [mem_ofPred_eq]
  refine ⟨fun h x hx ↦ ?_, fun h i hi ↦ Subgroup.mem_pontryaginAnnihilator.mpr fun b hb ↦ ?_⟩
  · -- Every local factor of `χ x` is trivial.
    rw [← (restrictedProductMulEquiv B).symm_apply_apply χ,
      restrictedProductMulEquiv_symm_apply_apply,
      finprod_eq_one_of_forall_eq_one fun i ↦ ?_]
    · exact Circle.one_mem_centeredArc_pi_div_two
    have hxi := RestrictedProduct.mem_box.mp hx i
    rw [restrictedProductMulEquiv_apply]
    by_cases hi : i ∈ T
    · rw [ite_eq_left hi] at hxi
      exact Subgroup.mem_pontryaginAnnihilator.mp (h i hi) _ hxi
    · rw [ite_eq_right hi, mem_singleton_iff] at hxi
      rw [hxi, _root_.map_one]
  · -- The powers of `χ` on `B i` stay in the half circle.
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
    rw [restrictMulSingle_apply_apply, ← map_pow, ← RestrictedProduct.mulSingle_pow]
    refine h (RestrictedProduct.mem_box.mpr fun j ↦ ?_)
    rcases eq_or_ne j i with rfl | hj
    · simpa [ite_eq_left hi] using (B j).pow_mem hb n
    · split_ifs <;> simp [RestrictedProduct.mulSingle_eq_of_ne _ _ hj]

/-- For a set `T` of indices on which every `B i` is compact, the characters of the restricted
product whose restriction to `G i` is trivial on `B i` for every `i ∈ T` form an open set. -/
theorem isOpen_setOf_forall_restrictMulSingle_mem {T : Set ι}
    (hT : ∀ i ∈ T, IsCompact (B i : Set (G i))) :
    IsOpen {χ : PontryaginDual (Πʳ i, [G i, B i]) |
      ∀ i ∈ T, restrictMulSingle B i χ ∈ (B i).pontryaginAnnihilator} := by
  classical
  rw [setOf_forall_restrictMulSingle_mem_eq_setOf_mapsTo]
  refine isOpen_setOfPred_mapsTo (RestrictedProduct.isCompact_box (fun i ↦ ?_)
    (.of_forall fun i ↦ ?_)) (Circle.isOpen_centeredArc _)
  · split_ifs with hi
    exacts [hT i hi, isCompact_singleton]
  · split_ifs
    · exact subset_rfl
    · exact singleton_subset_iff.mpr (B i).one_mem

/-- Restriction of characters to the factors is continuous from the Pontryagin dual of a
restricted product to the restricted product of the duals, as soon as cofinitely many reference
subgroups are compact. No openness of the reference subgroups is needed. -/
theorem continuous_restrictedProductMulEquiv
    (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i))) :
    Continuous (restrictedProductMulEquiv B) := by
  refine continuous_iff_continuousAt.mpr fun χ ↦ ?_
  -- Near `χ`, every character is trivial on `B i` wherever `χ` is and `B i` is compact.
  let T : Set ι := {i | IsCompact (B i : Set (G i)) ∧
    restrictMulSingle B i χ ∈ (B i).pontryaginAnnihilator}
  have hT : cofinite ≤ 𝓟 T :=
    le_principal_iff.mpr (hBc.and (eventually_restrictMulSingle_mem_pontryaginAnnihilator B χ))
  have hnhds := (isOpen_setOf_forall_restrictMulSingle_mem B (T := T) fun _ hi ↦ hi.1).mem_nhds
    fun _ hi ↦ hi.2
  refine (TauCeti.tendsto_restrictedProduct_iff_of_eventually_mem (l := 𝓝 χ)
    (f := restrictedProductMulEquiv B) hT (mem_of_superset hnhds fun φ hφ i hi ↦ by
      simpa only [restrictedProductMulEquiv_apply, SetLike.mem_coe] using hφ i hi)).mpr fun i ↦ ?_
  simp only [restrictedProductMulEquiv_apply]
  exact (map_continuous (restrictMulSingle B i)).tendsto χ

/-- Uniformly on a compact set `K`, the quotient of a local character `φ i` by `ψ i`, evaluated
at the `i`-th coordinate, tends to `1` as `φ` tends to `ψ` in the restricted product. -/
theorem tendsto_restrictedProduct_div_apply_nhds_one
    (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) {K : Set (Πʳ i, [G i, B i])}
    (hK : IsCompact K) (i : ι) :
    Tendsto (fun p : (Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) ×
        (Πʳ i, [G i, B i]) ↦ (p.1 i / ψ i) (p.2 i)) (𝓝 ψ ×ˢ 𝓟 K) (𝓝 1) := by
  intro V hV
  have hcont : Continuous fun φ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator] ↦
      φ i / ψ i :=
    (RestrictedProduct.continuous_eval i).div_const _
  have hlim : Tendsto (fun φ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator] ↦
      φ i / ψ i) (𝓝 ψ) (𝓝 1) := by
    simpa using hcont.tendsto ψ
  have hev := hlim.eventually
    (eventually_mapsTo_one (hK.image (RestrictedProduct.continuous_eval i)) hV)
  exact eventually_prod_principal_iff.mpr (hev.mono fun φ hφ x hx ↦ hφ (mem_image_of_mem _ hx))

/-- Assembling local characters by a finite product is continuous from the restricted product of
the duals to the Pontryagin dual of a restricted product, when every reference subgroup is open
and cofinitely many are compact. -/
theorem continuous_restrictedProductMulEquiv_symm
    (hBo : ∀ i, IsOpen (B i : Set (G i))) (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i))) :
    Continuous (restrictedProductMulEquiv B).symm := by
  classical
  refine continuous_iff_continuousAt.mpr fun ψ ↦ ?_
  refine (ContinuousMonoidHom.isInducing_toContinuousMap _ Circle).tendsto_nhds_iff.mpr
    (ContinuousMap.tendsto_nhds_compactOpen.mpr fun K hK U hU hKU ↦ ?_)
  -- Outside a finite set `S`, every point of `K` is integral, `B i` is compact and `ψ i` is
  -- trivial on `B i`.
  have hgood := (TauCeti.eventually_forall_mem_of_isCompact hBo hK).and (hBc.and ψ.eventually)
  set S := (mem_cofinite.mp hgood).toFinset
  have hS (i : ι) (hi : i ∉ S) : (∀ x ∈ K, x i ∈ B i) ∧ IsCompact (B i : Set (G i)) ∧
      ψ i ∈ (B i).pontryaginAnnihilator := by
    simpa [S] using hi
  -- Near `ψ`, every local character outside `S` is trivial on `B i`.
  have hbox : ∀ᶠ φ in 𝓝 ψ, ∀ i ∉ S, φ i ∈ (B i).pontryaginAnnihilator := by
    let C : ∀ i, Set (PontryaginDual (G i)) :=
      fun i ↦ if i ∈ S then univ else ((B i).pontryaginAnnihilator : Set _)
    have hopen : IsOpen (RestrictedProduct.box C :
        Set (Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator])) := by
      refine RestrictedProduct.isOpen_box (fun i ↦ ?_) (.of_forall fun i ↦ ?_)
      · by_cases hi : i ∈ S
        · simp only [C, hi, ite_true, isOpen_univ]
        · simpa only [C, hi, ite_false] using Subgroup.isOpen_pontryaginAnnihilator (hS i hi).2.1
      · by_cases hi : i ∈ S
        · simp only [C, hi, ite_true, subset_univ]
        · simp only [C, hi, ite_false, subset_rfl]
    have hψC : ψ ∈ RestrictedProduct.box C := RestrictedProduct.mem_box.mpr fun i ↦ by
      by_cases hi : i ∈ S
      · simp only [C, hi, ite_true, mem_univ]
      · simpa only [C, hi, ite_false, SetLike.mem_coe] using (hS i hi).2.2
    filter_upwards [hopen.mem_nhds hψC] with φ hφ i hi
    simpa only [C, hi, ite_false, SetLike.mem_coe] using RestrictedProduct.mem_box.mp hφ i
  -- Separate the compact image of `K` from the complement of `U`.
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_right
    (hK.image (map_continuous ((restrictedProductMulEquiv B).symm ψ))) hU hKU.image_subset
  have hprod := tendsto_finsetProd S fun i _ ↦ tendsto_restrictedProduct_div_apply_nhds_one B ψ hK i
  rw [Finset.prod_const_one] at hprod
  have hsmall := eventually_prod_principal_iff.mp (hprod hV)
  filter_upwards [hbox, hsmall] with φ hφ hφV x hx
  have hxS (i : ι) (hi : i ∉ S) : x i ∈ B i := (hS i hi).1 x hx
  have hψS (i : ι) (hi : i ∉ S) : ψ i ∈ (B i).pontryaginAnnihilator := (hS i hi).2.2
  have heq : (restrictedProductMulEquiv B).symm φ x =
      (restrictedProductMulEquiv B).symm ψ x * ∏ i ∈ S, (φ i / ψ i) (x i) := by
    simp only [restrictedProductMulEquiv_symm_apply_eq_prod B hφ hxS,
      restrictedProductMulEquiv_symm_apply_eq_prod B hψS hxS, div_eq_mul_inv, mul_apply,
      inv_apply, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_cancel_comm_assoc]
  change (restrictedProductMulEquiv B).symm φ x ∈ U
  rw [heq]
  exact hVU (mul_mem_mul (mem_image_of_mem _ hx) (hφV x hx))

/-- **Duality of restricted products.** For topological groups `G i` with open subgroups `B i`,
compact for all but finitely many `i`, restriction to the factors is an isomorphism of
topological groups from the Pontryagin dual of `Πʳ i, [G i, B i]` onto the restricted product of
the duals `PontryaginDual (G i)` with respect to the annihilators of the `B i`. -/
noncomputable def restrictedProductContinuousMulEquiv
    (hBo : ∀ i, IsOpen (B i : Set (G i))) (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i))) :
    PontryaginDual (Πʳ i, [G i, B i]) ≃ₜ*
      (Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) where
  toMulEquiv := restrictedProductMulEquiv B
  continuous_toFun := continuous_restrictedProductMulEquiv B hBc
  continuous_invFun := continuous_restrictedProductMulEquiv_symm B hBo hBc

/-- The underlying group isomorphism is `PontryaginDual.restrictedProductMulEquiv`. -/
@[simp]
theorem coe_restrictedProductContinuousMulEquiv
    (hBo : ∀ i, IsOpen (B i : Set (G i))) (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i))) :
    (restrictedProductContinuousMulEquiv B hBo hBc :
        PontryaginDual (Πʳ i, [G i, B i]) ≃*
          (Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator])) =
      restrictedProductMulEquiv B :=
  (rfl)

/-- Each coordinate of the image of a character is its restriction to the corresponding factor. -/
@[simp]
theorem restrictedProductContinuousMulEquiv_apply
    (hBo : ∀ i, IsOpen (B i : Set (G i))) (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (χ : PontryaginDual (Πʳ i, [G i, B i])) (i : ι) :
    restrictedProductContinuousMulEquiv B hBo hBc χ i = restrictMulSingle B i χ :=
  restrictedProductMulEquiv_apply B χ i

/-- The inverse isomorphism evaluates a family of local characters by the finite product of the
local values. -/
@[simp]
theorem restrictedProductContinuousMulEquiv_symm_apply_apply
    (hBo : ∀ i, IsOpen (B i : Set (G i))) (hBc : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) (x : Πʳ i, [G i, B i]) :
    (restrictedProductContinuousMulEquiv B hBo hBc).symm ψ x = ∏ᶠ i, ψ i (x i) :=
  restrictedProductMulEquiv_symm_apply_apply B ψ x

end PontryaginDual
