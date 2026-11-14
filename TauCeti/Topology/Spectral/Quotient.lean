/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallyProConstructible
import TauCeti.Topology.Spectral.Limits.Basic
import TauCeti.Topology.Spectral.PatchCriterion
import Mathlib.Topology.Maps.Strict.Basic
import Mathlib.Topology.WithTopology

/-!
# Quotients of spectral and locally spectral spaces by pro-constructible equivalence relations

Let `X` be a locally spectral space and `r` an equivalence relation on `X` whose graph
`R = {q : X × X | r q.1 q.2}` is locally pro-constructible and whose projections `R → X` lift
generalizations. Because `r` is symmetric, coordinate swap is a homeomorphism of `R` exchanging the
two projections, so the generalizing, spectral, and open-map conditions on the first projection are
each equivalent to the corresponding conditions on the second.

Even without ambient quasi-compactness or quasi-separatedness, `Quotient r` is T₀ and the quotient
map `Quotient.mk r : X → Quotient r` lifts generalizations. When the projections of `R` are also
quasi-compact (`IsSpectralMap`), every quasi-compact open subset `W ⊆ X` is contained in an open
`r`-saturated subset `U` bounded above by an `r`-saturated intersection of a nonempty family of
quasi-compact open subsets. Containment in the saturation of `W` itself fails in general, because
the saturation of a quasi-compact open need not be open.

Neither T₀ nor invariant neighbourhoods alone make `Quotient r` spectral: every compact Hausdorff
space arises as the quotient of a profinite space by a closed equivalence relation. Two criteria
supply the missing basis of opens with quasi-compact preimages:

* `TauCeti.spectralSpace_quotient`: when `X` is spectral, `R` is pro-constructible with
  generalizing projections, and `Quotient r` has a topological basis of opens with quasi-compact
  preimages in `X`, the quotient `Quotient r` is spectral (and `Quotient.mk r` is spectral by
  `TauCeti.isSpectralMap_of_isTopologicalBasis` and generalizing by
  `TauCeti.generalizingMap_quotient_mk`).
* `TauCeti.spectralSpace_quotient_of_isOpenMap` and
  `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`: when the projections `R → X` are open,
  generalization lifting is automatic on locally spectral spaces, `Quotient.mk r` is open and
  quasi-compact (hence locally spectral when `X` is quasi-separated), and `Quotient r` is
  quasi-separated and locally spectral — and spectral when `X` is spectral. This is the topological
  mechanism used to equip the underlying space of a spatial or locally spatial diamond with its
  spectral or locally spectral structure.

## Main definitions and results

* `Setoid.relSwap`: the coordinate-swap homeomorphism of `{q : X × X // r q.1 q.2}`.
* `TauCeti.generalizingMap_fst_iff_snd`, `TauCeti.isSpectralMap_fst_iff_snd`,
  `TauCeti.isOpenMap_fst_iff_snd`: equivalence of the two projections of `r`.
* `TauCeti.isOpenMap_quotient_mk_iff`: `Quotient.mk r` is open if and only if the projections of
  `r` are open.
* `TauCeti.generalizingMap_quotient_mk`: `Quotient.mk r` lifts generalizations.
* `TauCeti.t0Space_quotient`: `Quotient r` is a T₀ space.
* `TauCeti.exists_isOpen_saturated_between`,
  `TauCeti.exists_isOpen_and_sInter_isCompact_of_isCompact`: open `r`-saturated neighbourhoods
  bounded by `r`-saturated intersections of nonempty families of quasi-compact opens.
* `TauCeti.spectralSpace_quotient`: the spectral quotient criterion from a basis with
  quasi-compact preimages.
* `TauCeti.isSpectralMap_quotient_mk_of_isOpenMap`,
  `TauCeti.quasiSeparatedSpace_quotient_of_isOpenMap`,
  `TauCeti.spectralSpace_quotient_of_isOpenMap`,
  `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`: spectral and locally spectral quotients
  when the projections of `r` are open.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10,
  and Remark 2.8.
* The Stacks Project, Tags 0APA and 0APB (invariant open neighbourhoods for groupoids).
-/

public section

open Set Topology TopologicalSpace

section Projections

variable {X : Type*} [TopologicalSpace X]

/-- Coordinate swap on the graph `{q : X × X // r q.1 q.2}` of a `Setoid` is an involutive
homeomorphism exchanging the two projections to `X`. -/
def Setoid.relSwap (r : Setoid X) :
    {q : X × X // r q.1 q.2} ≃ₜ {q : X × X // r q.1 q.2} where
  toFun q := ⟨q.1.swap, r.symm q.2⟩
  invFun q := ⟨q.1.swap, r.symm q.2⟩
  left_inv q := Subtype.ext (Prod.swap_swap q.1)
  right_inv q := Subtype.ext (Prod.swap_swap q.1)
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

/-- Coercing `r.relSwap q` to the ambient product swaps its coordinates. -/
@[simp]
theorem Setoid.coe_relSwap_apply (r : Setoid X) (q : {q : X × X // r q.1 q.2}) :
    ((r.relSwap q : {q : X × X // r q.1 q.2}) : X × X) = q.1.swap := (rfl)

/-- `Setoid.relSwap` is its own inverse homeomorphism. -/
@[simp]
theorem Setoid.relSwap_symm (r : Setoid X) : r.relSwap.symm = r.relSwap := (rfl)

/-- Applying `Setoid.relSwap` twice is the identity. -/
@[simp]
theorem Setoid.relSwap_apply_relSwap (r : Setoid X) (q : {q : X × X // r q.1 q.2}) :
    r.relSwap (r.relSwap q) = q :=
  r.relSwap.symm_apply_apply q

end Projections

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-! ### Symmetry of the projections and openness of the quotient map -/

/-- By symmetry of `r`, the first projection of `{q : X × X // r q.1 q.2}` lifts generalizations
if and only if the second projection does. -/
theorem generalizingMap_fst_iff_snd {r : Setoid X} :
    GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ r.relSwap.isOpenEmbedding.generalizingMap.comp h,
    fun h ↦ r.relSwap.isOpenEmbedding.generalizingMap.comp h⟩

/-- By symmetry of `r`, the first projection of `{q : X × X // r q.1 q.2}` is spectral if and only
if the second projection is. -/
theorem isSpectralMap_fst_iff_snd {r : Setoid X} :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ h.comp r.relSwap.isProperMap.isSpectralMap,
    fun h ↦ h.comp r.relSwap.isProperMap.isSpectralMap⟩

/-- By symmetry of `r`, the first projection of `{q : X × X // r q.1 q.2}` is an open map if and
only if the second projection is. -/
theorem isOpenMap_fst_iff_snd {r : Setoid X} :
    IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ h.comp r.relSwap.isOpenMap, fun h ↦ h.comp r.relSwap.isOpenMap⟩

omit [TopologicalSpace X] in
/-- The `r`-saturation `Quotient.mk r ⁻¹' (Quotient.mk r '' W)` of a subset `W ⊆ X` is its
correspondence image under the two projections of `{q : X × X // r q.1 q.2}`. -/
theorem preimage_image_quotient_mk_eq_image_fst_preimage {r : Setoid X} (W : Set X) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' W) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
        ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' W) := by
  ext y
  simp only [mem_preimage, mem_image, Quotient.eq]
  exact ⟨fun ⟨x, hxW, hxy⟩ ↦ ⟨⟨(x, y), hxy⟩, hxW, rfl⟩,
    fun ⟨⟨⟨x, _⟩, hxy⟩, hxW, rfl⟩ ↦ ⟨x, hxW, hxy⟩⟩

/-- For any topological space `X` and `r : Setoid X`, the quotient map `Quotient.mk r` is open if
and only if the first projection `{q : X × X // r q.1 q.2} → X` is open. -/
theorem isOpenMap_quotient_mk_iff {r : Setoid X} :
    IsOpenMap (Quotient.mk r) ↔ IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) := by
  constructor
  · intro hq W hWo
    obtain ⟨Ω, hΩo, rfl⟩ := isOpen_induced_iff.mp hWo
    rw [isOpen_prod_iff] at hΩo
    refine isOpen_iff_forall_mem_open.mpr ?_
    rintro _ ⟨⟨⟨x, y⟩, hxy⟩, hxyΩ, rfl⟩
    obtain ⟨U, V, hUo, hVo, hxU, hyV, hUVΩ⟩ := hΩo x y hxyΩ
    refine ⟨U ∩ Quotient.mk r ⁻¹' (Quotient.mk r '' V), ?_,
      hUo.inter ((hq V hVo).preimage continuous_quotient_mk'),
      ⟨hxU, y, hyV, Quotient.sound (r.symm hxy)⟩⟩
    rintro x' ⟨hx'U, y', hy'V, hy'x'⟩
    exact ⟨⟨(x', y'), r.symm (Quotient.exact hy'x')⟩, hUVΩ ⟨hx'U, hy'V⟩, rfl⟩
  · intro hs U hUo
    rw [← (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage]
    change IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' U))
    rw [preimage_image_quotient_mk_eq_image_fst_preimage]
    exact isOpenMap_fst_iff_snd.mp hs _ (hUo.preimage (continuous_fst.comp continuous_subtype_val))

/-! ### Invariant closures, generalization lifting, and T₀ quotients -/

/-- On a locally spectral space, the closure of an `r`-invariant locally pro-constructible subset
remains `r`-invariant when the projections of `r` lift generalizations. -/
theorem closure_saturated_of_isLocallyProConstructible (hX : IsLocallySpectralSpace X)
    {r : Setoid X} {S : Set X} (hS : IsLocallyProConstructible S)
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hinv : ∀ ⦃x y⦄, r x y → x ∈ S → y ∈ S) :
    ∀ ⦃x y⦄, r x y → x ∈ closure S → y ∈ closure S := by
  rw [hS.closure_eq_setOfPred_specializes hX]
  rintro x y hxy ⟨w, hwS, hwx⟩
  obtain ⟨q', hq', hsq'⟩ := @hs ⟨(x, y), hxy⟩ w hwx
  refine ⟨q'.1.2, hinv q'.2 ((show q'.1.1 = w from hsq').symm ▸ hwS), ?_⟩
  exact hq'.map (continuous_snd.comp continuous_subtype_val)

/-- Saturation form of `TauCeti.closure_saturated_of_isLocallyProConstructible`. -/
theorem preimage_image_quotient_mk_closure_eq (hX : IsLocallySpectralSpace X) {r : Setoid X}
    {S : Set X} (hS : IsLocallyProConstructible S)
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hinv : Quotient.mk r ⁻¹' (Quotient.mk r '' S) = S) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' closure S) = closure S := by
  have hSinv : ∀ ⦃x y⦄, r x y → x ∈ S → y ∈ S := fun x y hxy hx ↦ by
    rw [← hinv]
    exact ⟨x, hx, Quotient.sound hxy⟩
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨x, hx, hxy⟩
  exact closure_saturated_of_isLocallyProConstructible hX hS hs hSinv (Quotient.exact hxy) hx

/-- On a locally spectral space, the quotient map by a locally pro-constructible equivalence
relation with generalizing projections lifts generalizations. -/
theorem generalizingMap_quotient_mk (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap (Quotient.mk r) := by
  intro x qy hqy
  induction qy using Quotient.ind with
  | _ y =>
    have horb : IsLocallyProConstructible {z : X | r y z} := hR.preimage_prodMkRight hX y
    have hcl_inv : ∀ ⦃u v⦄, r u v → u ∈ closure {z : X | r y z} → v ∈ closure {z : X | r y z} :=
      closure_saturated_of_isLocallyProConstructible hX horb hs fun _ _ huv hwu ↦ r.trans hwu huv
    have hxcl : x ∈ closure {z : X | r y z} := by
      by_contra hx
      let V : Set (Quotient r) := Quotient.mk r '' (closure {z : X | r y z})ᶜ
      have hpre : Quotient.mk r ⁻¹' V = (closure {z : X | r y z})ᶜ := by
        refine Subset.antisymm ?_ (subset_preimage_image _ _)
        rintro v ⟨u, hu, huv⟩ hv
        exact hu (hcl_inv (r.symm (Quotient.exact huv)) hv)
      have hVo : IsOpen V := by
        rw [← (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage]
        change IsOpen (Quotient.mk r ⁻¹' V)
        rw [hpre]
        exact isClosed_closure.isOpen_compl
      have hyV : Quotient.mk r y ∈ V := hqy.mem_open hVo ⟨x, hx, rfl⟩
      have hycompl : y ∈ Quotient.mk r ⁻¹' V := hyV
      rw [hpre] at hycompl
      exact hycompl (subset_closure (r.refl y))
    rw [horb.closure_eq_setOfPred_specializes hX] at hxcl
    obtain ⟨x', hyx', hx'x⟩ := hxcl
    exact ⟨x', hx'x, Quotient.sound (r.symm hyx')⟩

/-- The quotient of a locally spectral space by a locally pro-constructible equivalence relation
with generalizing projections is a T₀ space. -/
theorem t0Space_quotient (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    T0Space (Quotient r) := by
  have := hX.quasiSober
  have := hX.t0Space
  refine (t0Space_iff_inseparable (Quotient r)).mpr ?_
  rintro ⟨x⟩ ⟨y⟩ hxy
  have horb (a : X) : IsLocallyProConstructible {z : X | r a z} := hR.preimage_prodMkRight hX a
  have hcl_inv (a : X) :
      ∀ ⦃u v⦄, r u v → u ∈ closure {z : X | r a z} → v ∈ closure {z : X | r a z} :=
    closure_saturated_of_isLocallyProConstructible hX (horb a) hs fun _ _ huv hwu ↦ r.trans hwu huv
  have hmem_cl {a b : X} (hab : Inseparable (Quotient.mk r a) (Quotient.mk r b)) :
      b ∈ closure {z : X | r a z} := by
    by_contra hb
    let V : Set (Quotient r) := Quotient.mk r '' (closure {z : X | r a z})ᶜ
    have hpre : Quotient.mk r ⁻¹' V = (closure {z : X | r a z})ᶜ := by
      refine Subset.antisymm ?_ (subset_preimage_image _ _)
      rintro v ⟨u, hu, huv⟩ hv
      exact hu (hcl_inv a (r.symm (Quotient.exact huv)) hv)
    have hVo : IsOpen V := by
      rw [← (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage]
      change IsOpen (Quotient.mk r ⁻¹' V)
      rw [hpre]
      exact isClosed_closure.isOpen_compl
    have haV : Quotient.mk r a ∈ V :=
      (hab.mem_open_iff hVo).mpr ⟨b, hb, rfl⟩
    have hacompl : a ∈ Quotient.mk r ⁻¹' V := haV
    rw [hpre] at hacompl
    exact hacompl (subset_closure (r.refl a))
  have hZeq : closure {z : X | r x z} = closure {z : X | r y z} := by
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal (fun z hxz ↦ ?_) isClosed_closure
      exact hcl_inv y hxz (hmem_cl hxy.symm)
    · refine closure_minimal (fun z hyz ↦ ?_) isClosed_closure
      exact hcl_inv x hyz (hmem_cl hxy)
  let Z : Set X := closure {z : X | r x z}
  have : QuasiSober Z := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  let x₀ : Z := ⟨x, subset_closure (r.refl x)⟩
  let c : irreducibleComponents Z :=
    ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  let η : Z := (genericPoints.ofComponent c).1
  have hη : IsGenericPoint η c.1 := genericPoints.isGenericPoint_ofComponent c
  have hη_mem_orb {a : X} (hZa : Z = closure {z : X | r a z}) : r a η.1 := by
    have hηa : η.1 ∈ closure {z : X | r a z} := hZa ▸ η.2
    rw [(horb a).closure_eq_setOfPred_specializes hX] at hηa
    obtain ⟨w, haw, hwη⟩ := hηa
    let w₀ : Z := ⟨w, hZa.symm ▸ subset_closure haw⟩
    have hw₀η : w₀ ⤳ η := IsInducing.subtypeVal.specializes_iff.mp hwη
    have hc_sub : c.1 ⊆ closure ({w₀} : Set Z) := by
      rw [← hη.def]
      exact closure_minimal (singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hw₀η))
        isClosed_closure
    have hcl_eq : closure ({w₀} : Set Z) = c.1 :=
      eq_irreducibleComponent isIrreducible_singleton.isPreirreducible.closure hc_sub
    have hηw₀ : η ⤳ w₀ := by
      rw [specializes_iff_mem_closure, hη.def, ← hcl_eq]
      exact subset_closure (mem_singleton w₀)
    have hw_eq : w = η.1 := congrArg Subtype.val (hw₀η.antisymm hηw₀).eq
    exact hw_eq ▸ haw
  exact Quotient.sound (r.trans (hη_mem_orb rfl) (r.symm (hη_mem_orb hZeq)))

/-! ### Saturations and invariant open neighbourhoods -/

/-- When the projections of `r` are spectral, the `r`-saturation of any quasi-compact open subset
is quasi-compact. -/
theorem isCompact_preimage_image_quotient_mk {r : Setoid X}
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [preimage_image_quotient_mk_eq_image_fst_preimage]
  exact (hs_qc.isCompact_preimage_of_isOpen hWo hWc).image
    (continuous_snd.comp continuous_subtype_val)

/-- When the projections of `r` lift generalizations, the `r`-saturation of any subset stable
under generalization remains stable under generalization. -/
theorem stableUnderGeneralization_preimage_image_quotient_mk {r : Setoid X}
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWg : StableUnderGeneralization W) :
    StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [preimage_image_quotient_mk_eq_image_fst_preimage]
  refine (generalizingMap_fst_iff_snd.mp hs).stableUnderGeneralization_image ?_
  intro q q' hq'q hqW
  exact hWg (hq'q.map (continuous_fst.comp continuous_subtype_val)) hqW

/-- Given open subsets `W, W' ⊆ X` with the `r`-saturation of `W` contained in `W'`, removing the
closure of the `r`-saturation of `W'ᶜ` produces an open `r`-saturated neighbourhood `U` between
`W` and `W'`. -/
theorem exists_isOpen_saturated_between (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W W' : Set X} (hWo : IsOpen W) (hW'o : IsOpen W')
    (hWW' : Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W') :
    ∃ U : Set X, IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧ W ⊆ U ∧ U ⊆ W' := by
  let t : {q : X × X // r q.1 q.2} → X := fun q ↦ q.1.2
  let F : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W'ᶜ)
  have hR_ls : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have ht_ls : IsLocallySpectralMap t :=
    (isLocallySpectralMap_snd hX).comp (hX.prod hX) hR.isLocallySpectralMap_subtypeVal
  have ht_qc : IsSpectralMap t := isSpectralMap_fst_iff_snd.mp hs_qc
  have hF_lpc : IsLocallyProConstructible F := by
    dsimp only [F]
    rw [preimage_image_quotient_mk_eq_image_fst_preimage]
    exact (hW'o.isClosed_compl.preimage
      (continuous_fst.comp continuous_subtype_val)).isLocallyProConstructible.image hR_ls ht_ls
      ht_qc
  have hF_sat : Quotient.mk r ⁻¹' (Quotient.mk r '' F) = F := by
    rw [image_preimage_eq _ Quotient.mk_surjective]
  have hcl_sat : Quotient.mk r ⁻¹' (Quotient.mk r '' closure F) = closure F :=
    preimage_image_quotient_mk_closure_eq hX hF_lpc hs hF_sat
  refine ⟨(closure F)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_, ?_⟩
  · refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro y ⟨x, hx, hxy⟩ hycl
    have hxcl : x ∈ Quotient.mk r ⁻¹' (Quotient.mk r '' closure F) :=
      ⟨y, hycl, hxy.symm⟩
    rw [hcl_sat] at hxcl
    exact hx hxcl
  · have hdisj : Disjoint W F := by
      refine disjoint_left.mpr fun x hxW hxF ↦ ?_
      obtain ⟨y, hyW', hyx⟩ := hxF
      exact hyW' (hWW' ⟨x, hxW, hyx.symm⟩)
    exact fun x hxW hxcl ↦ (disjoint_left.mp (hdisj.closure_right hWo) hxW) hxcl
  · intro x hx
    by_contra hxW'
    exact hx (subset_closure (subset_preimage_image _ _ hxW'))

/-- **Invariant open neighbourhoods for pro-constructible equivalence relations.** On a locally
spectral space `X`, let `r` be a locally pro-constructible equivalence relation whose projections
are quasi-compact and lift generalizations. Every quasi-compact open subset `W ⊆ X` is contained
in an open `r`-saturated subset `U` bounded above by an `r`-saturated intersection of a nonempty
family of quasi-compact open subsets. -/
theorem exists_isOpen_and_sInter_isCompact_of_isCompact
    (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ (U : Set X) (ℬ : Set (Set X)),
      IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧
      ℬ.Nonempty ∧ (∀ O ∈ ℬ, IsOpen O ∧ IsCompact O) ∧
      Quotient.mk r ⁻¹' (Quotient.mk r '' ⋂₀ ℬ) = ⋂₀ ℬ ∧
      W ⊆ U ∧ U ⊆ ⋂₀ ℬ := by
  have := hX.prespectralSpace
  have hEc : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) :=
    isCompact_preimage_image_quotient_mk hs_qc hWo hWc
  have hcover_W :
      Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ ⋃ O ∈ {O : Set X | IsOpen O ∧ IsCompact O}, O := by
    intro x _
    obtain ⟨O, hO, hxO, -⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (mem_univ x) isOpen_univ
    exact mem_iUnion₂.mpr ⟨O, hO, hxO⟩
  obtain ⟨T, hTB, hTfin, hT⟩ :=
    hEc.elim_finite_subcover_image (b := {O : Set X | IsOpen O ∧ IsCompact O}) (c := id)
      (fun O hO ↦ hO.1) hcover_W
  let W' : Set X := ⋃ O ∈ T, O
  have hW'o : IsOpen W' := isOpen_biUnion fun O hO ↦ (hTB hO).1
  have hW'c : IsCompact W' := hTfin.isCompact_biUnion fun O hO ↦ (hTB hO).2
  obtain ⟨U, hUo, hUsat, hWU, hUW'⟩ :=
    exists_isOpen_saturated_between hX hR hs_qc hs hWo hW'o hT
  let E' : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W')
  have hE'c : IsCompact E' := isCompact_preimage_image_quotient_mk hs_qc hW'o hW'c
  have hE'g : StableUnderGeneralization E' :=
    stableUnderGeneralization_preimage_image_quotient_mk hs hW'o.stableUnderGeneralization
  have hE'sat : Quotient.mk r ⁻¹' (Quotient.mk r '' E') = E' := by
    rw [image_preimage_eq _ Quotient.mk_surjective]
  let ℬ : Set (Set X) := {O : Set X | IsOpen O ∧ IsCompact O ∧ E' ⊆ O}
  have hE'_eq : E' = ⋂₀ ℬ := hE'c.eq_sInter_of_stableUnderGeneralization hE'g
  have hℬ_ne : ℬ.Nonempty := by
    have hcover_E' : E' ⊆ ⋃ O ∈ {O : Set X | IsOpen O ∧ IsCompact O}, O := by
      intro x _
      obtain ⟨O, hO, hxO, -⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (mem_univ x) isOpen_univ
      exact mem_iUnion₂.mpr ⟨O, hO, hxO⟩
    obtain ⟨T', hT'B, hT'fin, hT'⟩ :=
      hE'c.elim_finite_subcover_image (b := {O : Set X | IsOpen O ∧ IsCompact O}) (c := id)
        (fun O hO ↦ hO.1) hcover_E'
    exact ⟨⋃ O ∈ T', O, isOpen_biUnion fun O hO ↦ (hT'B hO).1,
      hT'fin.isCompact_biUnion fun O hO ↦ (hT'B hO).2, hT'⟩
  refine ⟨U, ℬ, hUo, hUsat, hℬ_ne, fun O hO ↦ ⟨hO.1, hO.2.1⟩, ?_, hWU, ?_⟩
  · rwa [← hE'_eq]
  · rw [← hE'_eq]
    exact hUW'.trans (subset_preimage_image _ _)

/-! ### The spectral quotient criterion and the open-projection case -/

/-- **The spectral quotient criterion.** Let `X` be a spectral space and `r` an equivalence
relation whose graph is pro-constructible in `X × X` and whose projections lift generalizations. If
the quotient topology on `Quotient r` admits a basis `B` of opens whose preimages in `X` are
quasi-compact, then `Quotient r` is a spectral space. Moreover `Quotient.mk r` is spectral by
`TauCeti.isSpectralMap_of_isTopologicalBasis` and lifts generalizations by
`TauCeti.generalizingMap_quotient_mk`. -/
theorem spectralSpace_quotient [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hBc : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) := by
  have : T0Space (Quotient r) :=
    t0Space_quotient SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible hs
  have hXcomp : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
      (constructibleTopology X) WithTopology.ofTopology
      (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have hcomp : @CompactSpace (Quotient r)
      (TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X)) :=
    @Function.Surjective.compactSpace X (Quotient r) (constructibleTopology X)
      (TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X))
      (Quotient.mk r) (@continuous_coinduced_rng X (Quotient r) (Quotient.mk r)
        (constructibleTopology X))
      hXcomp Quotient.mk_surjective
  refine spectralSpace_of_isClopen_generateFrom
    (t' := TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X))
    hB.eq_generateFrom hcomp fun V hV ↦ ?_
  have hVc := (hBc V hV).isClopen_constructibleTopology_of_isOpen
    ((hB.isOpen hV).preimage continuous_quotient_mk')
  let : TopologicalSpace X := constructibleTopology X
  let : TopologicalSpace (Quotient r) :=
    TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X)
  exact ⟨isClosed_coinduced.mpr hVc.isClosed, isOpen_coinduced.mpr hVc.isOpen⟩

/-- On a prespectral space, if the projections of `r` are quasi-compact and open, then the
quotient map `Quotient.mk r` is spectral (`IsSpectralMap`). -/
theorem isSpectralMap_quotient_mk_of_isOpenMap [PrespectralSpace X] {r : Setoid X}
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsSpectralMap (Quotient.mk r) := by
  have hq_open : IsOpenMap (Quotient.mk r) := isOpenMap_quotient_mk_iff.mpr hs_open
  refine isSpectralMap_of_isTopologicalBasis
    (PrespectralSpace.isTopologicalBasis.quotient hq_open) continuous_quotient_mk' ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  exact isCompact_preimage_image_quotient_mk hs_qc hWo hWc

/-- On a quasi-separated prespectral space, if the projections of `r` are quasi-compact and open,
then `Quotient r` is quasi-separated. -/
theorem quasiSeparatedSpace_quotient_of_isOpenMap [PrespectralSpace X] [QuasiSeparatedSpace X]
    {r : Setoid X} (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    QuasiSeparatedSpace (Quotient r) := by
  have hq_open : IsOpenMap (Quotient.mk r) := isOpenMap_quotient_mk_iff.mpr hs_open
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun W : {W : Set X // IsOpen W ∧ IsCompact W} ↦ Quotient.mk r '' W.1)
    (by
      have h := PrespectralSpace.isTopologicalBasis.quotient hq_open
      rwa [Set.image_eq_range] at h)
    fun ⟨W₁, hW₁o, hW₁c⟩ ⟨W₂, hW₂o, hW₂c⟩ ↦ ?_
  have h₁o : IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' W₁)) :=
    (hq_open W₁ hW₁o).preimage continuous_quotient_mk'
  have h₂o : IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' W₂)) :=
    (hq_open W₂ hW₂o).preimage continuous_quotient_mk'
  have h₁c := isCompact_preimage_image_quotient_mk hs_qc hW₁o hW₁c
  have h₂c := isCompact_preimage_image_quotient_mk hs_qc hW₂o hW₂c
  have hinter : Quotient.mk r '' W₁ ∩ Quotient.mk r '' W₂ =
      Quotient.mk r ''
        (Quotient.mk r ⁻¹' (Quotient.mk r '' W₁) ∩ Quotient.mk r ⁻¹' (Quotient.mk r '' W₂)) := by
    rw [← preimage_inter, image_preimage_eq _ Quotient.mk_surjective]
  rw [hinter]
  exact (QuasiSeparatedSpace.inter_isCompact _ _ h₁o h₁c h₂o h₂c).image continuous_quotient_mk'

/-- Let `X` be a spectral space and `r` a pro-constructible equivalence relation on `X` whose
projections `{q : X × X // r q.1 q.2} → X` are open. Then `Quotient r` is a spectral space. -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    SpectralSpace (Quotient r) := by
  have : SpectralSpace {q : X × X // r q.1 q.2} := hR.spectralSpace
  have hs_qc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hs_gen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
    hs_qc.generalizingMap_of_isOpenMap hs_open
  have hq_open : IsOpenMap (Quotient.mk r) := isOpenMap_quotient_mk_iff.mpr hs_open
  refine spectralSpace_quotient hR hs_gen (PrespectralSpace.isTopologicalBasis.quotient hq_open) ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  exact isCompact_preimage_image_quotient_mk hs_qc hWo hWc

/-- Let `X` be a quasi-separated locally spectral space and `r` a locally pro-constructible
equivalence relation on `X` whose projections `{q : X × X // r q.1 q.2} → X` are quasi-compact and
open. Then `Quotient r` is locally spectral. Together with
`TauCeti.quasiSeparatedSpace_quotient_of_isOpenMap`, `TauCeti.isOpenMap_quotient_mk_iff`,
`TauCeti.isSpectralMap_quotient_mk_of_isOpenMap`, and `IsSpectralMap.isLocallySpectralMap`, this
shows that `Quotient r` is quasi-separated and locally spectral and `Quotient.mk r` is open,
quasi-compact, and locally spectral. -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallySpectralSpace (Quotient r) := by
  have hq_open : IsOpenMap (Quotient.mk r) := isOpenMap_quotient_mk_iff.mpr hs_open
  refine isLocallySpectralSpace_iff.mpr fun y ↦ ?_
  induction y using Quotient.ind with
  | _ x =>
    obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
    have hWc : IsCompact W := isCompact_iff_compactSpace.mpr hWs.toCompactSpace
    let U₀ : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W)
    have hU₀o : IsOpen U₀ := (hq_open W hWo).preimage continuous_quotient_mk'
    have hU₀c : IsCompact U₀ := isCompact_preimage_image_quotient_mk hs_qc hWo hWc
    have : CompactSpace U₀ := isCompact_iff_compactSpace.mp hU₀c
    have : QuasiSeparatedSpace U₀ := hU₀o.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
    have hU₀s : SpectralSpace U₀ :=
      spectralSpace_iff_isLocallySpectralSpace.mpr
        ⟨hU₀o.isOpenEmbedding_subtypeVal.isLocallySpectralSpace hX, inferInstance, inferInstance⟩
    let r₀ : Setoid U₀ := r.comap Subtype.val
    have hR₀ : IsProConstructible {p : U₀ × U₀ | r₀ p.1 p.2} := by
      let e := Homeomorph.Set.prod U₀ U₀
      have : CompactSpace ↥(U₀ ×ˢ U₀) := e.symm.compactSpace
      have : SpectralSpace ↥(U₀ ×ˢ U₀) := e.isOpenEmbedding.spectralSpace
      exact (hR.isProConstructible_preimage (hU₀o.prod hU₀o)).preimage
        e.symm.isProperMap.isSpectralMap
    have hs₀_open : IsOpenMap (fun p : {p : U₀ × U₀ // r₀ p.1 p.2} ↦ p.1.1) := by
      let ι : {p : U₀ × U₀ // r₀ p.1 p.2} → {q : X × X // r q.1 q.2} :=
        fun p ↦ ⟨(p.1.1.1, p.1.2.1), p.2⟩
      have hι_emb : IsEmbedding ι := by
        refine .of_comp ?_ continuous_subtype_val
          ((IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal)
        exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
      have hι_range : range ι = (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' U₀ := by
        ext ⟨⟨a, b⟩, hab⟩
        simp only [mem_range, mem_preimage, ι, Subtype.ext_iff, Prod.ext_iff]
        refine ⟨fun ⟨p, hp1, _⟩ ↦ hp1 ▸ p.1.1.2, fun haU₀ ↦ ?_⟩
        have hbU₀ : b ∈ U₀ := by
          obtain ⟨w, hwW, hwa⟩ := haU₀
          exact ⟨w, hwW, hwa.trans (Quotient.sound hab)⟩
        exact ⟨⟨(⟨a, haU₀⟩, ⟨b, hbU₀⟩), hab⟩, rfl, rfl⟩
      have hι_open : IsOpenEmbedding ι :=
        ⟨hι_emb, hι_range ▸ hU₀o.preimage (continuous_fst.comp continuous_subtype_val)⟩
      intro O hOo
      have heq : (fun p : {p : U₀ × U₀ // r₀ p.1 p.2} ↦ p.1.1) '' O =
          (Subtype.val : U₀ → X) ⁻¹'
            ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) '' (ι '' O)) := by
        ext u
        simp only [mem_image, mem_preimage, ι]
        exact ⟨fun ⟨p, hpO, hpu⟩ ↦ ⟨_, ⟨p, hpO, rfl⟩, congrArg Subtype.val hpu⟩,
          fun ⟨_, ⟨p, hpO, rfl⟩, hpu⟩ ↦ ⟨p, hpO, Subtype.ext hpu⟩⟩
      rw [heq]
      exact (hs_open _ (hι_open.isOpenMap O hOo)).preimage continuous_subtype_val
    have : SpectralSpace (Quotient r₀) := spectralSpace_quotient_of_isOpenMap hR₀ hs₀_open
    let f : U₀ → Quotient r := Quotient.mk r ∘ Subtype.val
    have hf_strict : Topology.IsStrictMap f :=
      (hq_open.comp hU₀o.isOpenMap_subtype_val).isStrictMap
        (continuous_quotient_mk'.comp continuous_subtype_val)
    have hrange : range f = Quotient.mk r '' W := by
      rw [range_comp, Subtype.range_coe_subtype, ofPred_mem_eq,
        image_preimage_eq _ Quotient.mk_surjective]
    let eQ : Quotient r₀ ≃ₜ ↥(Quotient.mk r '' W) :=
      ((Homeomorph.Quotient.congrRight
        (fun u₁ u₂ ↦ show r u₁.1 u₂.1 ↔ Quotient.mk r u₁.1 = Quotient.mk r u₂.1
          from Quotient.eq.symm)).trans
        (Homeomorph.quotientKerEquivRange hf_strict)).trans (Homeomorph.setCongr hrange)
    have : CompactSpace ↥(Quotient.mk r '' W) := eQ.compactSpace
    exact ⟨Quotient.mk r '' W, hq_open W hWo, ⟨x, hxW, rfl⟩,
      eQ.symm.isOpenEmbedding.spectralSpace⟩

end TauCeti

end
