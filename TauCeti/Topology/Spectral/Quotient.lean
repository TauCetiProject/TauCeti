/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Maps.OpenQuotient
public import TauCeti.Topology.Spectral.LocallyProConstructible
import TauCeti.Topology.Sober
import TauCeti.Topology.Spectral.Limits.Basic
import TauCeti.Topology.Spectral.PatchCriterion
import Mathlib.Topology.WithTopology

/-!
# Quotients of spectral and locally spectral spaces by pro-constructible equivalence relations

Let `X` be a spectral or locally spectral space and `r : Setoid X` an equivalence relation whose
graph `{q : X × X | r q.1 q.2}` is pro-constructible or locally pro-constructible in `X × X`.
Because the swap involution `Setoid.swapHomeomorph` is a homeomorphism of `{q : X × X // r q.1 q.2}`
interchanging the two projections, spectrality, local spectrality, openness, and the generalizing
property are symmetric between the first and second projections.

When `X` is locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible, and the first
projection from `{q : X × X // r q.1 q.2}` to `X` is generalizing:
* every `r`-equivalence class is locally pro-constructible in `X`, hence locally spectral, sober,
  and T₀;
* the closure of any `r`-invariant locally pro-constructible subset of `X` remains `r`-invariant
  (`TauCeti.IsLocallyProConstructible.preimage_image_quotientMk_closure`);
* the quotient map `Quotient.mk r : X → Quotient r` is generalizing
  (`TauCeti.generalizingMap_quotientMk`) and `Quotient r` is T₀ (`TauCeti.t0Space_quotient`),
  without any global compactness or quasiseparatedness assumption on `X`.

Assuming in addition that the first projection is quasi-compact (`IsSpectralMap`), `r`-saturations
preserve local pro-constructibility (`TauCeti.IsLocallyProConstructible.preimage_image_quotientMk`).
Taking complements of closures of saturations produces `r`-invariant open neighbourhoods between
any `r`-invariant generalization-stable set and any open set containing it
(`TauCeti.exists_isOpen_preimage_image_quotientMk_eq_between`), expressing the saturation of every
quasi-compact open set as an intersection of `r`-invariant open neighbourhoods contained in
quasi-compact opens (`TauCeti.preimage_image_quotientMk_eq_sInter`).

Globally on a spectral space `X`, if `{q : X × X | r q.1 q.2}` is pro-constructible, the first
projection is generalizing, and `Quotient r` admits a topological basis whose preimages under
`Quotient.mk r` are quasi-compact, then `Quotient r` is spectral (`TauCeti.spectralSpace_quotient`):
the topology coinduced on `Quotient r` from the constructible topology of `X` is compact and makes
each basis element clopen, so `TauCeti.spectralSpace_of_isClopen_generateFrom` applies.

Finally, when the first projection from `{q : X × X // r q.1 q.2}` to `X` is an open map, it is
automatically generalizing (`TauCeti.generalizingMap_fst_of_isOpenMap`). On a spectral space `X`
this makes `Quotient r` spectral with spectral quotient map
(`TauCeti.spectralSpace_quotient_of_isOpenMap`). On any locally spectral space `X`, restricting `r`
to spectral open charts via `IsOpen.quotientComapHomeomorphImage` — without requiring the charts to
be `r`-invariant — shows that `Quotient r` is locally spectral and quasiseparated and that
`Quotient.mk r` is locally spectral (`TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`,
`TauCeti.quasiSeparatedSpace_quotient_of_isOpenMap`,
`TauCeti.isLocallySpectralMap_quotientMk_of_isOpenMap`).

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10.
* [The Stacks Project, Tags 0APA and 0APB](https://stacks.math.columbia.edu/tag/0APA).
-/

public section

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

namespace Setoid

/-- On the graph of an equivalence relation, the second projection is a spectral map if and only if
the first projection is. -/
theorem isSpectralMap_snd_iff_fst (r : Setoid X) :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ↔
      IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) := by
  have hswap : IsSpectralMap r.swapHomeomorph := r.swapHomeomorph.isProperMap.isSpectralMap
  constructor
  · intro h
    convert h.comp hswap using 1
    ext q
    exact (r.snd_swapHomeomorph q).symm
  · intro h
    convert h.comp hswap using 1
    ext q
    exact (r.fst_swapHomeomorph q).symm

/-- On the graph of an equivalence relation, the second projection is locally spectral if and only
if the first projection is. -/
theorem isLocallySpectralMap_snd_iff_fst (r : Setoid X) :
    TauCeti.IsLocallySpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ↔
      TauCeti.IsLocallySpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) := by
  have heq : (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ∘ r.swapHomeomorph :=
    funext fun q ↦ (r.fst_swapHomeomorph q).symm
  rw [heq, r.swapHomeomorph.isLocallySpectralMap_comp_iff]

end Setoid

namespace IsSpectralMap

/-- If the first projection from `{q : X × X // r q.1 q.2}` is a spectral map, then the saturation
of every quasi-compact open subset of `X` is quasi-compact. -/
theorem isCompact_preimage_image_quotientMk {r : Setoid X}
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) {W : Set X} (hWo : IsOpen W)
    (hWc : IsCompact W) : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [r.preimage_image_quotientMk]
  exact (hs.isCompact_preimage_of_isOpen hWo hWc).image (continuous_snd.comp continuous_subtype_val)

/-- On a prespectral space, if the first projection from `{q : X × X // r q.1 q.2}` is both a
spectral map and an open map, then `Quotient.mk r : X → Quotient r` is a spectral map. -/
theorem isSpectralMap_quotientMk_of_isOpenMap [PrespectralSpace X] {r : Setoid X}
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsSpectralMap (Quotient.mk r) := by
  refine ⟨continuous_quot_mk, fun U hUo hUc ↦ ?_⟩
  obtain ⟨V, hVc, rfl⟩ := (r.isOpenMap_quotientMk hs_open).exists_opens_image_eq_of_prespectralSpace
    continuous_quot_mk (Quotient.mk_surjective.range_eq.symm ▸ subset_univ _) hUo hUc
  exact hs_qc.isCompact_preimage_image_quotientMk V.2 hVc

end IsSpectralMap

namespace TauCeti

/-! ### Generalizing projections and T₀ quotients -/

/-- Every equivalence class of a locally pro-constructible equivalence relation on a locally
spectral space is locally pro-constructible. -/
theorem IsLocallyProConstructible.setOfPred_rel {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) (hX : IsLocallySpectralSpace X)
    (x : X) : IsLocallyProConstructible {y : X | r x y} :=
  hR.preimage_prodMk_right hX x

/-- When `X` is locally spectral and the first projection from `{q : X × X // r q.1 q.2}` is
generalizing, the closure of any `r`-invariant locally pro-constructible subset `F ⊆ X` is again
`r`-invariant. -/
theorem IsLocallyProConstructible.preimage_image_quotientMk_closure {F : Set X}
    (hF : IsLocallyProConstructible F) (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hFinv : Quotient.mk r ⁻¹' (Quotient.mk r '' F) = F) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' closure F) = closure F := by
  refine Subset.antisymm (fun y ⟨y', hy', hy'y⟩ ↦ ?_) (subset_preimage_image _ _)
  rw [hF.closure_eq_setOfPred_specializes hX] at hy' ⊢
  obtain ⟨x', hx'F, hx'y'⟩ := hy'
  let q₀ : {q : X × X // r q.1 q.2} := ⟨(y', y), Quotient.exact hy'y⟩
  obtain ⟨q₁, hq₁q₀, hq₁fst⟩ := hs (a := q₀) hx'y'
  refine ⟨q₁.1.2, ?_, hq₁q₀.map (continuous_snd.comp continuous_subtype_val)⟩
  rw [← hFinv]
  exact ⟨x', hx'F, Quotient.sound (hq₁fst ▸ q₁.2)⟩

private theorem exists_minimal_rel {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) (hX : IsLocallySpectralSpace X)
    (x : X) : ∃ η : X, r x η ∧ ∀ ξ : X, r x ξ → ξ ⤳ η → ξ = η := by
  let S := {y : X | r x y}
  have hS : IsLocallySpectralSpace S := (hR.setOfPred_rel hX x).isLocallySpectralSpace hX
  have : QuasiSober S := hS.quasiSober
  have : T0Space S := hS.t0Space
  let s₀ : S := ⟨x, r.refl x⟩
  let C : irreducibleComponents S :=
    ⟨irreducibleComponent s₀, irreducibleComponent_mem_irreducibleComponents s₀⟩
  let η := genericPoints.ofComponent C
  refine ⟨η.1.1, η.1.2, fun ξ hξ hξη ↦ ?_⟩
  have hspec : (⟨ξ, hξ⟩ : S) ⤳ η.1 := IsInducing.subtypeVal.specializes_iff.mp hξη
  exact congrArg Subtype.val (mem_genericPoints_iff.mp η.2 ⟨ξ, hξ⟩ hspec)

/-- If `X` is locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible, and the
first projection from `{q : X × X // r q.1 q.2}` is generalizing, then `Quotient.mk r` is a
generalizing map. -/
theorem generalizingMap_quotientMk (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap (Quotient.mk r) := by
  intro y abar habar
  obtain ⟨a, rfl⟩ := Quotient.exists_rep abar
  have hO : IsLocallyProConstructible {z : X | r a z} := hR.setOfPred_rel hX a
  have hcl : Quotient.mk r ⁻¹' (Quotient.mk r '' closure {z : X | r a z}) =
      closure {z : X | r a z} :=
    hO.preimage_image_quotientMk_closure hX hs (r.preimage_image_quotientMk_setOfPred_rel a)
  have hclosed : IsClosed (Quotient.mk r '' closure {z : X | r a z}) := by
    rw [← r.isQuotientMap_quotientMk.isClosed_preimage, hcl]
    exact isClosed_closure
  have hy_img : Quotient.mk r y ∈ Quotient.mk r '' closure {z : X | r a z} :=
    specializes_iff_forall_closed.mp habar _ hclosed ⟨a, subset_closure (r.refl a), rfl⟩
  have hy_cl : y ∈ closure {z : X | r a z} := hcl ▸ hy_img
  rw [hO.closure_eq_setOfPred_specializes hX] at hy_cl
  obtain ⟨x, hax, hxy⟩ := hy_cl
  exact ⟨x, hxy, (Quotient.sound hax).symm⟩

/-- If `X` is locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible, and the
first projection from `{q : X × X // r q.1 q.2}` is generalizing, then `Quotient r` is a T₀ space
(Scholze, *Étale cohomology of diamonds*, Lemma 2.7, first assertion). -/
theorem t0Space_quotient (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    T0Space (Quotient r) := by
  have : T0Space X := hX.t0Space
  have hgen := generalizingMap_quotientMk hX hR hs
  rw [t0Space_iff_inseparable]
  refine Quotient.ind₂ fun x y hxy ↦ ?_
  obtain ⟨η, hyη, hηmin⟩ := exists_minimal_rel hR hX y
  have hmk_y : Quotient.mk r η = Quotient.mk r y := (Quotient.sound hyη).symm
  have hxη : Quotient.mk r x ⤳ Quotient.mk r η := hmk_y ▸ hxy.specializes
  obtain ⟨ω, hωη, hmk_ω⟩ := hgen hxη
  have hηω : Quotient.mk r η ⤳ Quotient.mk r ω := by
    rw [hmk_ω, hmk_y]
    exact hxy.symm.specializes
  obtain ⟨ξ, hξω, hmk_ξ⟩ := hgen hηω
  have hyξ : r y ξ := r.trans hyη (Quotient.exact hmk_ξ.symm)
  have hξη : ξ = η := hηmin ξ hyξ (hξω.trans hωη)
  have hω_eq : ω = η := (hωη.antisymm (hξη ▸ hξω)).eq
  rw [← hmk_ω, hω_eq, hmk_y]

/-! ### Invariant open neighbourhoods of saturations -/

/-- When `X` is locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible, and the
first projection is a spectral map, the `r`-saturation of every locally pro-constructible subset of
`X` is locally pro-constructible. -/
theorem IsLocallyProConstructible.preimage_image_quotientMk {F : Set X}
    (hF : IsLocallyProConstructible F) (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallyProConstructible (Quotient.mk r ⁻¹' (Quotient.mk r '' F)) := by
  rw [r.preimage_image_quotientMk]
  exact (hF.preimage hX (hR.isLocallySpectralMap_fst hX)).image
    (hR.isLocallySpectralSpace (hX.prod hX)) (hR.isLocallySpectralMap_snd hX)
    (r.isSpectralMap_snd_iff_fst.mpr hs_qc)

/-- Between any `r`-invariant generalization-stable subset `E ⊆ X` and any open subset `W' ⊇ E`,
there is an `r`-invariant open subset `U` with `E ⊆ U ⊆ W'`. -/
theorem exists_isOpen_preimage_image_quotientMk_eq_between (hX : IsLocallySpectralSpace X)
    {r : Setoid X} (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {E W' : Set X} (hEinv : Quotient.mk r ⁻¹' (Quotient.mk r '' E) = E)
    (hEgen : StableUnderGeneralization E) (hW'o : IsOpen W') (hEW' : E ⊆ W') :
    ∃ U : Set X, IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧ E ⊆ U ∧ U ⊆ W' := by
  let F := Quotient.mk r ⁻¹' (Quotient.mk r '' W'ᶜ)
  have hF : IsLocallyProConstructible F :=
    hW'o.isClosed_compl.isLocallyProConstructible.preimage_image_quotientMk hX hR hs_qc
  have hFinv : Quotient.mk r ⁻¹' (Quotient.mk r '' F) = F := by
    dsimp [F]
    rw [Quotient.mk_surjective.image_preimage]
  have hcl_inv : Quotient.mk r ⁻¹' (Quotient.mk r '' closure F) = closure F :=
    hF.preimage_image_quotientMk_closure hX hs_gen hFinv
  refine ⟨(closure F)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_, ?_⟩
  · refine Subset.antisymm (fun x ⟨y, hy, hyx⟩ hycl ↦ hy ?_) (subset_preimage_image _ _)
    rw [← hcl_inv]
    exact ⟨x, hycl, hyx.symm⟩
  · intro y hyE hycl
    rw [hF.closure_eq_setOfPred_specializes hX] at hycl
    obtain ⟨x, ⟨z, hzW', hzx⟩, hxy⟩ := hycl
    have hxE : x ∈ E := hEgen hxy hyE
    have hzE : z ∈ E := hEinv ▸ ⟨x, hxE, hzx.symm⟩
    exact hzW' (hEW' hzE)
  · rw [compl_subset_comm]
    exact (subset_preimage_image (Quotient.mk r) W'ᶜ).trans subset_closure

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.7** (intersection form): on a locally
spectral space `X`, when `{q : X × X | r q.1 q.2}` is locally pro-constructible and the first
projection is generalizing and quasi-compact (`IsSpectralMap`), the `r`-saturation of any
quasi-compact open subset `W ⊆ X` is the intersection of the `r`-invariant open subsets containing
it that are themselves contained in quasi-compact opens. -/
theorem preimage_image_quotientMk_eq_sInter (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' W) =
      ⋂₀ {U : Set X | IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧
        Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ U ∧
        ∃ W', IsOpen W' ∧ IsCompact W' ∧ U ⊆ W'} := by
  have : PrespectralSpace X := hX.prespectralSpace
  have hEc : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) :=
    hs_qc.isCompact_preimage_image_quotientMk hWo hWc
  have hEinv :
      Quotient.mk r ⁻¹' (Quotient.mk r '' (Quotient.mk r ⁻¹' (Quotient.mk r '' W))) =
        Quotient.mk r ⁻¹' (Quotient.mk r '' W) := by
    rw [Quotient.mk_surjective.image_preimage]
  have hEgen : StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) :=
    hWo.stableUnderGeneralization_preimage_image_quotientMk hs_gen
  refine Subset.antisymm (subset_sInter fun _ hU ↦ hU.2.2.1) fun x hx ↦ ?_
  rw [hEc.eq_sInter_of_stableUnderGeneralization hEgen]
  refine mem_sInter.mpr fun W' ⟨hW'o, hW'c, hEW'⟩ ↦ ?_
  obtain ⟨U, hUo, hUinv, hEU, hUW'⟩ :=
    exists_isOpen_preimage_image_quotientMk_eq_between hX hR hs_gen hs_qc hEinv hEgen hW'o hEW'
  exact hUW' (mem_sInter.mp hx U ⟨hUo, hUinv, hEU, W', hW'o, hW'c, hUW'⟩)

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.7** (sandwich form): every quasi-compact open
`W ⊆ X` is contained in an `r`-invariant open subset `U` inside a quasi-compact open `W'` whose
`r`-saturation is the intersection of all quasi-compact opens containing it. -/
theorem exists_isOpen_preimage_image_quotientMk_subset_sInter (hX : IsLocallySpectralSpace X)
    {r : Setoid X} (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ U W' : Set X, IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧
      IsOpen W' ∧ IsCompact W' ∧ W ⊆ U ∧ U ⊆ W' ∧
      Quotient.mk r ⁻¹' (Quotient.mk r '' W') =
        ⋂₀ {V : Set X | IsOpen V ∧ IsCompact V ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' W') ⊆ V} := by
  have : PrespectralSpace X := hX.prespectralSpace
  have hEc : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) :=
    hs_qc.isCompact_preimage_image_quotientMk hWo hWc
  have hEinv :
      Quotient.mk r ⁻¹' (Quotient.mk r '' (Quotient.mk r ⁻¹' (Quotient.mk r '' W))) =
        Quotient.mk r ⁻¹' (Quotient.mk r '' W) := by
    rw [Quotient.mk_surjective.image_preimage]
  have hEgen : StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) :=
    hWo.stableUnderGeneralization_preimage_image_quotientMk hs_gen
  obtain ⟨W', hW'c, hW'o, hEW', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc isOpen_univ (subset_univ _)
  obtain ⟨U, hUo, hUinv, hEU, hUW'⟩ :=
    exists_isOpen_preimage_image_quotientMk_eq_between hX hR hs_gen hs_qc hEinv hEgen hW'o hEW'
  have hE'c : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W')) :=
    hs_qc.isCompact_preimage_image_quotientMk hW'o hW'c
  have hE'gen : StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W')) :=
    hW'o.stableUnderGeneralization_preimage_image_quotientMk hs_gen
  exact ⟨U, W', hUo, hUinv, hW'o, hW'c, (subset_preimage_image _ _).trans hEU, hUW',
    hE'c.eq_sInter_of_stableUnderGeneralization hE'gen⟩

/-! ### Global spectral quotient criterion -/

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.9**: let `X` be a spectral space and
`r : Setoid X` an equivalence relation whose graph `{q : X × X | r q.1 q.2}` is pro-constructible in
`X × X` and whose first projection is generalizing. If `Quotient r` admits a topological basis `B`
such that `Quotient.mk r ⁻¹' b` is quasi-compact for every `b ∈ B`, then `Quotient r` is a spectral
space. -/
theorem spectralSpace_quotient [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hpre : ∀ b ∈ B, IsCompact (Quotient.mk r ⁻¹' b)) :
    SpectralSpace (Quotient r) := by
  have hX : IsLocallySpectralSpace X := SpectralSpace.isLocallySpectralSpace
  have hT0 : T0Space (Quotient r) := t0Space_quotient hX hR.isLocallyProConstructible hs
  have htB : instTopologicalSpaceQuotient (s := r) = generateFrom B := hB.eq_generateFrom
  have hopen (b : Set (Quotient r)) (hb : b ∈ B) : IsOpen (Quotient.mk r ⁻¹' b) :=
    (hB.isOpen hb).preimage continuous_quot_mk
  let t' : TopologicalSpace (Quotient r) := coinduced (Quotient.mk r) (constructibleTopology X)
  have hcompX : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
      (constructibleTopology X) WithTopology.ofTopology
      (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have hcomp : @CompactSpace (Quotient r) t' :=
    @Function.Surjective.compactSpace X (Quotient r) (constructibleTopology X) t'
      (Quotient.mk r) (@continuous_coinduced_rng X (Quotient r) (Quotient.mk r)
        (constructibleTopology X)) hcompX Quotient.mk_surjective
  refine @spectralSpace_of_isClopen_generateFrom (Quotient r) B t'
    (instTopologicalSpaceQuotient (s := r)) htB hcomp ?_ hT0
  intro b hb
  have hcl : @IsClopen X (constructibleTopology X) (Quotient.mk r ⁻¹' b) :=
    (hpre b hb).isClopen_constructibleTopology_of_isOpen (hopen b hb)
  exact ⟨isClosed_coinduced.mpr hcl.1, isOpen_coinduced.mpr hcl.2⟩

/-! ### Open-projection quotients -/

/-- When `X` is locally spectral and `{q : X × X | r q.1 q.2}` is locally pro-constructible, an
open first projection is automatically generalizing. -/
theorem generalizingMap_fst_of_isOpenMap (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 := by
  intro q b hbq
  let fst : {q : X × X // r q.1 q.2} → X := fun p ↦ p.1.1
  have hfib : IsLocallyProConstructible (fst ⁻¹' {b}) :=
    (isLocallyProConstructible_singleton b).preimage hX (hR.isLocallySpectralMap_fst hX)
  have hR_sp : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have hq_cl : q ∈ closure (fst ⁻¹' {b}) := by
    refine mem_closure_iff.mpr fun O hOo hqO ↦ ?_
    obtain ⟨p, hpO, hpb⟩ :=
      specializes_iff_forall_open.mp hbq (fst '' O) (hs_open O hOo) ⟨q, hqO, rfl⟩
    exact ⟨p, hpO, hpb⟩
  rw [hfib.closure_eq_setOfPred_specializes hR_sp] at hq_cl
  obtain ⟨p, hpb, hpq⟩ := hq_cl
  exact ⟨p, hpq, hpb⟩

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.10** (global case): if `X` is spectral,
`{q : X × X | r q.1 q.2}` is pro-constructible in `X × X`, and the first projection from
`{q : X × X // r q.1 q.2}` to `X` is an open map, then `Quotient r` is a spectral space. -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    SpectralSpace (Quotient r) := by
  have hX : IsLocallySpectralSpace X := SpectralSpace.isLocallySpectralSpace
  have hs_gen := generalizingMap_fst_of_isOpenMap hX hR.isLocallyProConstructible hs_open
  have hB :
      IsTopologicalBasis (Set.image (Quotient.mk r) '' {W : Set X | IsOpen W ∧ IsCompact W}) :=
    (r.isOpenQuotientMap_quotientMk hs_open).isTopologicalBasis
      (PrespectralSpace.isTopologicalBasis (X := X))
  refine spectralSpace_quotient hR hs_gen hB ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  exact hR.isSpectralMap_fst.isCompact_preimage_image_quotientMk hWo hWc

/-- Restricting a locally pro-constructible equivalence relation to a spectral open subset `W ⊆ X`
yields a pro-constructible equivalence relation on `W`. -/
theorem IsLocallyProConstructible.isProConstructible_comap {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) {W : Set X} (hWo : IsOpen W)
    [SpectralSpace W] :
    IsProConstructible {q : W × W | (r.comap (Subtype.val : W → X)) q.1 q.2} := by
  let eWW := Homeomorph.Set.prod W W
  have : CompactSpace (W ×ˢ W : Set (X × X)) := eWW.symm.compactSpace
  have : SpectralSpace (W ×ˢ W : Set (X × X)) := eWW.isOpenEmbedding.spectralSpace
  convert (hR.isProConstructible_preimage (hWo.prod hWo)).preimage
    eWW.symm.isProperMap.isSpectralMap using 1
  ext ⟨w₁, w₂⟩
  rfl

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.10** (local space assertion): if `X` is
locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible in `X × X`, and the first
projection from `{q : X × X // r q.1 q.2}` to `X` is an open map, then `Quotient r` is locally
spectral. -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap (hX : IsLocallySpectralSpace X)
    {r : Setoid X} (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallySpectralSpace (Quotient r) := by
  have hq_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotientMk hs_open
  refine isLocallySpectralSpace_iff.mpr fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
  have := hWs
  have : SpectralSpace (Quotient (r.comap (Subtype.val : W → X))) :=
    spectralSpace_quotient_of_isOpenMap (hR.isProConstructible_comap hWo)
      (hWo.isOpenMap_fst_comap hs_open)
  let e := hWo.quotientComapHomeomorphImage hq_open
  have : CompactSpace (Quotient.mk r '' W) := e.compactSpace
  exact ⟨Quotient.mk r '' W, hq_open W hWo, ⟨x, hxW, rfl⟩, e.symm.isOpenEmbedding.spectralSpace⟩

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.10** (local map assertion): if `X` is
locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible in `X × X`, and the first
projection from `{q : X × X // r q.1 q.2}` to `X` is an open map, then
`Quotient.mk r : X → Quotient r` is locally spectral. -/
theorem isLocallySpectralMap_quotientMk_of_isOpenMap (hX : IsLocallySpectralSpace X)
    {r : Setoid X} (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallySpectralMap (Quotient.mk r) := by
  have hq_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotientMk hs_open
  refine IsLocallySpectralMap.of_forall_exists fun x ↦ ?_
  obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
  have := hWs
  let rW := r.comap (Subtype.val : W → X)
  have hRW : IsProConstructible {q : W × W | rW q.1 q.2} := hR.isProConstructible_comap hWo
  have hsW : IsOpenMap (fun q : {q : W × W // rW q.1 q.2} ↦ q.1.1) :=
    hWo.isOpenMap_fst_comap hs_open
  have : SpectralSpace (Quotient rW) := spectralSpace_quotient_of_isOpenMap hRW hsW
  let e := hWo.quotientComapHomeomorphImage hq_open
  have hmaps : MapsTo (Quotient.mk r) W (Quotient.mk r '' W) := mapsTo_image _ _
  refine ⟨W, Quotient.mk r '' W, hmaps, hWo, hq_open W hWo, hxW, inferInstance, ?_⟩
  have hfac : hmaps.restrict (Quotient.mk r) W (Quotient.mk r '' W) = e ∘ Quotient.mk rW :=
    funext fun w ↦ Subtype.ext (hWo.coe_quotientComapHomeomorphImage_mk hq_open w).symm
  rw [hfac]
  exact e.isProperMap.isSpectralMap.comp
    (hRW.isSpectralMap_fst.isSpectralMap_quotientMk_of_isOpenMap hsW)

/-- **Scholze, *Étale cohomology of diamonds*, Lemma 2.10** (quasiseparatedness assertion): if `X`
is locally spectral, `{q : X × X | r q.1 q.2}` is locally pro-constructible in `X × X`, and the
first projection from `{q : X × X // r q.1 q.2}` to `X` is an open map, then `Quotient r` is
quasiseparated, without any global quasiseparatedness or quasi-compactness assumption on `X` or the
projections. -/
theorem quasiSeparatedSpace_quotient_of_isOpenMap (hX : IsLocallySpectralSpace X)
    {r : Setoid X} (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    QuasiSeparatedSpace (Quotient r) := by
  let b : {W : Set X // IsOpen W ∧ SpectralSpace W} → Set (Quotient r) :=
    fun W ↦ Quotient.mk r '' W.1
  have hb : IsTopologicalBasis (range b) := by
    convert (r.isOpenQuotientMap_quotientMk hs_open).isTopologicalBasis hX.isTopologicalBasis
      using 1
    ext U
    exact ⟨fun ⟨W, hUW⟩ ↦ ⟨W.1, W.2, hUW⟩, fun ⟨W, hW, hUW⟩ ↦ ⟨⟨W, hW⟩, hUW⟩⟩
  refine QuasiSeparatedSpace.of_isTopologicalBasis hb fun W₁ W₂ ↦ ?_
  have := W₁.2.2
  have := W₂.2.2
  let e := Homeomorph.Set.prod W₁.1 W₂.1
  have : CompactSpace (W₁.1 ×ˢ W₂.1 : Set (X × X)) := e.symm.compactSpace
  have : SpectralSpace (W₁.1 ×ˢ W₂.1 : Set (X × X)) := e.isOpenEmbedding.spectralSpace
  let P : Set (W₁.1 ×ˢ W₂.1 : Set (X × X)) := Subtype.val ⁻¹' {q : X × X | r q.1 q.2}
  have hPc : IsCompact P := (hR.isProConstructible_preimage (W₁.2.1.prod W₂.2.1)).isCompact
  have heq : b W₁ ∩ b W₂ =
      (fun p : (W₁.1 ×ˢ W₂.1 : Set (X × X)) ↦ Quotient.mk r p.1.1) '' P := by
    ext z
    constructor
    · rintro ⟨⟨x₁, hx₁W, rfl⟩, ⟨x₂, hx₂W, hx₂⟩⟩
      exact ⟨⟨(x₁, x₂), hx₁W, hx₂W⟩, Quotient.exact hx₂.symm, rfl⟩
    · rintro ⟨⟨⟨x₁, x₂⟩, hx₁W, hx₂W⟩, hr, rfl⟩
      exact ⟨⟨x₁, hx₁W, rfl⟩, ⟨x₂, hx₂W, (Quotient.sound hr).symm⟩⟩
  rw [heq]
  exact hPc.image (continuous_quot_mk.comp (continuous_fst.comp continuous_subtype_val))

end TauCeti
