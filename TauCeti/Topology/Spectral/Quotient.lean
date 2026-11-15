/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.Basic
public import TauCeti.Topology.Spectral.Limits.Basic
public import TauCeti.Topology.Spectral.LocallyProConstructible
import Mathlib.Topology.LocalAtTarget

/-!
# Spectral and locally spectral quotients by pro-constructible equivalence relations

Let `X` be a locally spectral topological space and `r : Setoid X` an equivalence relation whose
graph `R = {q : X × X | r q.1 q.2}` is locally pro-constructible in `X × X` and whose projections
`R → X` are quasi-compact (`IsSpectralMap`) and generalizing (`GeneralizingMap`). By symmetry of
`r`, each projection property holds for the first projection if and only if it holds for the second,
so the hypotheses below ask only for the first projection.

Under these hypotheses alone, saturations of locally pro-constructible subsets remain locally
pro-constructible, closures of saturated locally pro-constructible subsets remain saturated, the
quotient map `Quotient.mk r : X → Quotient r` lifts generalizations, the quotient `Quotient r` is
`T0Space`, and every quasi-compact open `W ⊆ X` admits an `r`-saturated open neighbourhood `U`
between `W` and any chosen quasi-compact open `W'` containing the saturation of `W` (and hence
contained in the `r`-saturated intersection of quasi-compact opens
`Quotient.mk r ⁻¹' (Quotient.mk r '' W')`).

These hypotheses do not by themselves make `Quotient r` spectral: every compact Hausdorff space
arises as a quotient of a profinite space by a closed equivalence relation, whose projections are
automatically spectral and generalizing. Spectrality of `Quotient r` holds under either of two
additional conditions:

1. **The basis criterion** (`Setoid.spectralSpace_quotient`): when `X` is spectral and `Quotient r`
   admits a topological basis whose inverse images under `Quotient.mk r` are quasi-compact,
   `Quotient r` is a spectral space (and `Quotient.mk r` is spectral by
   `TauCeti.isSpectralMap_of_isTopologicalBasis` and generalizing by
   `Setoid.generalizingMap_quotientMk`).
2. **The open-projection criterion** (`Setoid.isLocallySpectralSpace_quotient_of_isOpenMap` and
   `Setoid.spectralSpace_quotient_of_isOpenMap`): when `X` is quasiseparated and locally spectral
   and the graph projection `R → X` is quasi-compact and open, openness forces the projection to be
   generalizing (`TauCeti.IsLocallySpectralMap.generalizingMap_of_isOpenMap`) and makes
   `Quotient.mk r` an open, quasi-compact, locally spectral quotient map onto a quasiseparated
   locally spectral space `Quotient r` (hence spectral when `X` is spectral). This is the
   topological quotient theorem used to equip spatial diamonds and locally spatial geometric
   quotients with their underlying locally spectral spaces.

## Main results

* `Setoid.isSpectralMap_fst_iff_snd`: symmetry of quasi-compactness between the two projections of
  the graph of `r`, complementing `Setoid.generalizingMap_fst_iff_snd` and
  `Setoid.isOpenMap_fst_iff_snd`.
* `Setoid.isLocallyProConstructible_preimage_image_quotientMk`: the `r`-saturation of a locally
  pro-constructible subset is locally pro-constructible.
* `Setoid.preimage_image_quotientMk_closure`: the closure of an `r`-saturated locally
  pro-constructible subset is `r`-saturated.
* `Setoid.generalizingMap_quotientMk_of_isLocallySpectralSpace` and
  `Setoid.generalizingMap_quotientMk`: `Quotient.mk r` lifts generalizations.
* `Setoid.t0Space_quotient_of_isLocallySpectralSpace` and `Setoid.t0Space_quotient`: `Quotient r`
  is `T0Space`.
* `Setoid.exists_isOpen_preimage_image_eq_subset` and
  `Setoid.exists_isCompact_isOpen_and_isOpen_preimage_image_eq`: existence of `r`-saturated open
  neighbourhoods of quasi-compact opens inside `r`-saturated intersections of quasi-compact opens.
* `Setoid.spectralSpace_quotient`: the spectral quotient criterion from a basis with quasi-compact
  preimages.
* `Setoid.isSpectralMap_quotientMk_of_isOpenMap`,
  `Setoid.quasiSeparatedSpace_quotient_of_isOpenMap`,
  `Setoid.isLocallySpectralSpace_quotient_of_isOpenMap`, and
  `Setoid.spectralSpace_quotient_of_isOpenMap`: the open-projection quotient criteria in the locally
  spectral and spectral settings.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10, and
  Remark 2.8.
* The Stacks Project, tags 0APA and 0APB (scheme-theoretic invariant open neighbourhoods).
-/

public section

open Set Topology TopologicalSpace TauCeti

namespace Setoid

variable {X : Type*} [TopologicalSpace X] (r : Setoid X)

/-! ### Symmetry and local spectrality of the graph projections -/

/-- By symmetry of `r`, the first projection of `{q : X × X // r q.1 q.2}` is a spectral map if and
only if the second projection is. -/
theorem isSpectralMap_fst_iff_snd :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) := by
  have heq₁ : (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ∘ r.swapGraphHomeomorph := by
    funext q
    exact (congrArg Prod.fst (r.coe_swapGraphHomeomorph_apply q)).symm
  have heq₂ : (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ∘ r.swapGraphHomeomorph := by
    funext q
    exact (congrArg Prod.snd (r.coe_swapGraphHomeomorph_apply q)).symm
  exact ⟨fun h ↦ heq₁ ▸ h.comp r.swapGraphHomeomorph.isProperMap.isSpectralMap,
    fun h ↦ heq₂ ▸ h.comp r.swapGraphHomeomorph.isProperMap.isSpectralMap⟩

/-- When `X` is spectral and the graph of `r` is pro-constructible in `X × X`, the first projection
of the graph is automatically a spectral map. -/
theorem isSpectralMap_fst [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2}) :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
  isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal

/-- When `X` is spectral and the graph of `r` is pro-constructible in `X × X`, the second
projection of the graph is automatically a spectral map. -/
theorem isSpectralMap_snd [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2}) :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  r.isSpectralMap_fst_iff_snd.mp (r.isSpectralMap_fst hR)

/-- On a locally spectral space, the graph `{q : X × X // r q.1 q.2}` of a locally
pro-constructible equivalence relation is locally spectral. -/
theorem isLocallySpectralSpace_graph (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) :
    IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
  hR.isLocallySpectralSpace (hX.prod hX)

/-- On a locally spectral space, the first projection of a locally pro-constructible equivalence
relation is a locally spectral map. -/
theorem isLocallySpectralMap_fst (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) :
    IsLocallySpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
  (hX.isLocallySpectralMap_fst hX).comp (hX.prod hX)
    (hR.isLocallySpectralMap_subtypeVal (hX.prod hX))

/-- On a locally spectral space, the second projection of a locally pro-constructible equivalence
relation is a locally spectral map. -/
theorem isLocallySpectralMap_snd (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) :
    IsLocallySpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  (hX.isLocallySpectralMap_snd hX).comp (hX.prod hX)
    (hR.isLocallySpectralMap_subtypeVal (hX.prod hX))

/-! ### Saturations, orbit closures, `T0Space`, and invariant open neighbourhoods -/

/-- If `X` is locally spectral, the graph of `r` is locally pro-constructible, and its first
projection is quasi-compact, then the `r`-saturation of any locally pro-constructible subset of `X`
is locally pro-constructible. -/
theorem isLocallyProConstructible_preimage_image_quotientMk (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {s : Set X} (hs : IsLocallyProConstructible s) :
    IsLocallyProConstructible (Quotient.mk r ⁻¹' (Quotient.mk r '' s)) := by
  rw [r.preimage_image_quotientMk_eq_image_snd]
  exact (hs.preimage hX (r.isLocallySpectralMap_fst hX hR)).image
    (r.isLocallySpectralSpace_graph hX hR) (r.isLocallySpectralMap_snd hX hR)
    (r.isSpectralMap_fst_iff_snd.mp hqc)

/-- On a locally spectral space, if the first projection of `r` lifts generalizations, then the
closure of any `r`-saturated locally pro-constructible subset is again `r`-saturated. -/
theorem preimage_image_quotientMk_closure (hX : IsLocallySpectralSpace X)
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {s : Set X} (hs : IsLocallyProConstructible s)
    (hsat : Quotient.mk r ⁻¹' (Quotient.mk r '' s) = s) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' closure s) = closure s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rw [hs.closure_eq_setOfPred_specializes hX]
  rintro z' ⟨z, ⟨y, hy, hyz⟩, hzz'⟩
  obtain ⟨q, hq, hqy⟩ := @hgen ⟨(z, z'), Quotient.exact hzz'⟩ y hyz
  have hysnd : q.1.2 ∈ s := by
    rw [← hsat]
    exact ⟨y, hy, Quotient.sound (hqy ▸ q.2)⟩
  exact ⟨q.1.2, hysnd, hq.map (continuous_snd.comp continuous_subtype_val)⟩

/-- Every equivalence class `{y : X | r x y}` of a locally pro-constructible equivalence relation
with quasi-compact projection on a locally spectral space is locally pro-constructible. -/
theorem isLocallyProConstructible_setOf_rel (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) (x : X) :
    IsLocallyProConstructible {y : X | r x y} := by
  have heq : {y : X | r x y} = Quotient.mk r ⁻¹' (Quotient.mk r '' {x}) := by
    ext y
    simp only [mem_ofPred_eq, image_singleton, mem_preimage, mem_singleton_iff, Quotient.eq]
    exact ⟨r.symm, r.symm⟩
  rw [heq]
  exact r.isLocallyProConstructible_preimage_image_quotientMk hX hR hqc
    (isLocallyProConstructible_singleton x)

private theorem preimage_image_quotientMk_closure_setOf_rel (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) (x : X) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' closure {y : X | r x y}) = closure {y : X | r x y} := by
  refine r.preimage_image_quotientMk_closure hX hgen
    (r.isLocallyProConstructible_setOf_rel hX hR hqc x) ?_
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro z ⟨y, hxy, hyz⟩
  exact r.trans hxy (Quotient.exact hyz)

private theorem isClosed_image_quotientMk_closure_setOf_rel (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) (x : X) :
    IsClosed (Quotient.mk r '' closure {y : X | r x y}) := by
  have hq : IsQuotientMap (Quotient.mk r) := isQuotientMap_quotient_mk'
  rw [← hq.isClosed_preimage, r.preimage_image_quotientMk_closure_setOf_rel hX hR hqc hgen x]
  exact isClosed_closure

private theorem mem_closure_setOf_rel_of_specializes (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) {x y : X}
    (hxy : Quotient.mk r x ⤳ Quotient.mk r y) :
    y ∈ closure {w : X | r x w} := by
  rw [← r.preimage_image_quotientMk_closure_setOf_rel hX hR hqc hgen x]
  exact hxy.mem_closed (r.isClosed_image_quotientMk_closure_setOf_rel hX hR hqc hgen x)
    ⟨x, subset_closure (r.refl x), rfl⟩

private theorem closure_setOf_rel_subset_of_specializes (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) {x y : X}
    (hxy : Quotient.mk r x ⤳ Quotient.mk r y) :
    closure {w : X | r y w} ⊆ closure {w : X | r x w} := by
  refine closure_minimal (fun w hyw ↦ ?_) isClosed_closure
  rw [← r.preimage_image_quotientMk_closure_setOf_rel hX hR hqc hgen x]
  exact ⟨y, r.mem_closure_setOf_rel_of_specializes hX hR hqc hgen hxy, Quotient.sound hyw⟩

/-- On a locally spectral space, if the graph of `r` is locally pro-constructible and its first
projection is quasi-compact and generalizing, then `Quotient.mk r` lifts generalizations. -/
theorem generalizingMap_quotientMk_of_isLocallySpectralSpace (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    GeneralizingMap (Quotient.mk r) := by
  intro z q hqz
  induction q using Quotient.inductionOn with | h y => ?_
  have hz_cl := r.mem_closure_setOf_rel_of_specializes hX hR hqc hgen hqz
  rw [(r.isLocallyProConstructible_setOf_rel hX hR hqc y).closure_eq_setOfPred_specializes hX]
    at hz_cl
  obtain ⟨x, hyx, hxz⟩ := hz_cl
  exact ⟨x, hxz, Quotient.sound (r.symm hyx)⟩

/-- **Quotient `T0Space` theorem** (Scholze, *Étale cohomology of diamonds*, Lemma 2.7). On a
locally spectral space `X`, the quotient by a locally pro-constructible equivalence relation whose
first projection is quasi-compact and generalizing is a `T0Space`. -/
theorem t0Space_quotient_of_isLocallySpectralSpace (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    T0Space (Quotient r) := by
  have _ : QuasiSober X := hX.quasiSober
  have _ : T0Space X := hX.t0Space
  refine (t0Space_iff_inseparable (Quotient r)).mpr fun q₁ q₂ h12 ↦ ?_
  induction q₁ using Quotient.inductionOn with | h x => ?_
  induction q₂ using Quotient.inductionOn with | h y => ?_
  have hZeq : closure {w : X | r x w} = closure {w : X | r y w} :=
    Subset.antisymm (r.closure_setOf_rel_subset_of_specializes hX hR hqc hgen h12.specializes')
      (r.closure_setOf_rel_subset_of_specializes hX hR hqc hgen h12.specializes)
  let Z : Set X := closure {w : X | r x w}
  have _ : QuasiSober Z := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  let C : Set Z := irreducibleComponent ⟨x, subset_closure (r.refl x)⟩
  have hCi : IsIrreducible C := isIrreducible_irreducibleComponent
  let η : Z := hCi.genericPoint
  have hη : IsGenericPoint η C := hCi.isGenericPoint_genericPoint isClosed_irreducibleComponent
  have hmem_orbit {u : X} (hu : η.1 ∈ closure {w : X | r u w})
      (hsub : closure {w : X | r u w} ⊆ Z) : r u η.1 := by
    rw [(r.isLocallyProConstructible_setOf_rel hX hR hqc u).closure_eq_setOfPred_specializes hX]
      at hu
    obtain ⟨w, huw, hwη⟩ := hu
    let wZ : Z := ⟨w, hsub (subset_closure huw)⟩
    have hwηZ : wZ ⤳ η := IsEmbedding.subtypeVal.isInducing.specializes_iff.mp hwη
    have hCsub : C ⊆ closure ({wZ} : Set Z) := hη.def ▸ hwηZ.closure_subset
    have hcl_eq : closure ({wZ} : Set Z) = C :=
      eq_irreducibleComponent (isIrreducible_singleton (x := wZ)).closure.isPreirreducible hCsub
    have hweq : w = η.1 := congrArg Subtype.val ((isGenericPoint_def.mpr hcl_eq).eq hη)
    exact hweq ▸ huw
  exact Quotient.sound (r.trans (hmem_orbit η.2 Subset.rfl)
    (r.symm (hmem_orbit (hZeq ▸ η.2) hZeq.symm.subset)))

/-- If the first projection of the graph of `r` is quasi-compact, then the `r`-saturation of every
quasi-compact open subset of `X` is quasi-compact. -/
theorem isCompact_preimage_image_quotientMk
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [r.preimage_image_quotientMk_eq_image_snd]
  exact (hqc.isCompact_preimage_of_isOpen hWo hWc).image
    (continuous_snd.comp continuous_subtype_val)

/-- If the first projection of the graph of `r` lifts generalizations, then the `r`-saturation of
every subset stable under generalization is stable under generalization. -/
theorem stableUnderGeneralization_preimage_image_quotientMk
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {W : Set X} (hWg : StableUnderGeneralization W) :
    StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [r.preimage_image_quotientMk_eq_image_snd]
  exact (hWg.preimage (continuous_fst.comp continuous_subtype_val)).image
    (r.generalizingMap_fst_iff_snd.mp hgen)

/-- On a prespectral space, if the first projection of `r` is quasi-compact and generalizing, then
the `r`-saturation of any quasi-compact open `W ⊆ X` is the intersection of the nonempty family of
quasi-compact opens containing it. -/
theorem preimage_image_quotientMk_eq_sInter [PrespectralSpace X]
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' W) =
      ⋂₀ {V : Set X | IsOpen V ∧ IsCompact V ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ V} :=
  (r.isCompact_preimage_image_quotientMk hqc hWo hWc).eq_sInter_of_stableUnderGeneralization
    (r.stableUnderGeneralization_preimage_image_quotientMk hgen hWo.stableUnderGeneralization)

/-- **Invariant open neighbourhood lemma** (Scholze, *Étale cohomology of diamonds*, Lemma 2.7).
Let `W` and `W'` be open subsets of a locally spectral space `X` such that `W'` contains the
`r`-saturation of `W`. Under a locally pro-constructible equivalence relation with quasi-compact,
generalizing first projection, there is an open `r`-saturated subset `U` with `W ⊆ U` and
`U ⊆ W'` (hence `U ⊆ Quotient.mk r ⁻¹' (Quotient.mk r '' W')`). -/
theorem exists_isOpen_preimage_image_eq_subset (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {W W' : Set X} (hWo : IsOpen W) (hW'o : IsOpen W')
    (hWW' : Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W') :
    ∃ U : Set X, IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧ W ⊆ U ∧ U ⊆ W' := by
  let F : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W'ᶜ)
  have hFpro : IsLocallyProConstructible F :=
    r.isLocallyProConstructible_preimage_image_quotientMk hX hR hqc
      hW'o.isClosed_compl.isLocallyProConstructible
  have hFsat : Quotient.mk r ⁻¹' (Quotient.mk r '' F) = F := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro z ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    exact ⟨x, hx, hxy.trans hyz⟩
  have hclFsat : Quotient.mk r ⁻¹' (Quotient.mk r '' closure F) = closure F :=
    r.preimage_image_quotientMk_closure hX hgen hFpro hFsat
  refine ⟨(closure F)ᶜ, isClosed_closure.isOpen_compl,
    r.preimage_image_quotientMk_compl hclFsat, ?_, ?_⟩
  · have hdisj : Disjoint W F := disjoint_left.mpr fun w hw ⟨x, hxW', hxw⟩ ↦
      hxW' (hWW' ⟨w, hw, hxw.symm⟩)
    exact subset_compl_iff_disjoint_right.mpr (hdisj.closure_right hWo)
  · exact compl_subset_comm.mp ((subset_preimage_image (Quotient.mk r) W'ᶜ).trans subset_closure)

/-- For any quasi-compact open `W` of a locally spectral space `X`, there exist a quasi-compact open
`W'` containing the `r`-saturation of `W` and an open `r`-saturated subset `U` with
`W ⊆ U ⊆ W' ⊆ Quotient.mk r ⁻¹' (Quotient.mk r '' W')`, where the outer saturation is a nonempty
intersection of quasi-compact opens (`Setoid.preimage_image_quotientMk_eq_sInter`). -/
theorem exists_isCompact_isOpen_and_isOpen_preimage_image_eq (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ W' U : Set X, IsOpen W' ∧ IsCompact W' ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W' ∧
      IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧ W ⊆ U ∧ U ⊆ W' := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  obtain ⟨W', hW'c, hW'o, hWW', -⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (r.isCompact_preimage_image_quotientMk hqc hWo hWc) isOpen_univ (subset_univ _)
  obtain ⟨U, hUo, hUsat, hWU, hUW'⟩ :=
    r.exists_isOpen_preimage_image_eq_subset hX hR hqc hgen hWo hW'o hWW'
  exact ⟨W', U, hW'o, hW'c, hWW', hUo, hUsat, hWU, hUW'⟩

/-! ### Global spectral quotients (Scholze, Lemma 2.9) -/

/-- On a spectral space `X`, if the graph of `r` is pro-constructible in `X × X` and its first
projection lifts generalizations, then `Quotient r` is a `T0Space`. -/
theorem t0Space_quotient [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    T0Space (Quotient r) :=
  r.t0Space_quotient_of_isLocallySpectralSpace SpectralSpace.isLocallySpectralSpace
    hR.isLocallyProConstructible (r.isSpectralMap_fst hR) hs

/-- On a spectral space `X`, if the graph of `r` is pro-constructible in `X × X` and its first
projection lifts generalizations, then `Quotient.mk r` lifts generalizations. -/
theorem generalizingMap_quotientMk [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    GeneralizingMap (Quotient.mk r) :=
  r.generalizingMap_quotientMk_of_isLocallySpectralSpace SpectralSpace.isLocallySpectralSpace
    hR.isLocallyProConstructible (r.isSpectralMap_fst hR) hs

/-- **The spectral quotient criterion** (Scholze, *Étale cohomology of diamonds*, Lemma 2.9).
Let `X` be a spectral space and `r : Setoid X` an equivalence relation whose graph is
pro-constructible in `X × X` and whose first projection lifts generalizations (and hence so does the
second, by `Setoid.generalizingMap_fst_iff_snd`). If `Quotient r` admits a topological basis `B`
whose members pull back to quasi-compact subsets of `X`, then `Quotient r` is a spectral space.

Together with `TauCeti.isSpectralMap_of_isTopologicalBasis` (which gives
`IsSpectralMap (Quotient.mk r)` from `hB` and `hpre` alone) and `Setoid.generalizingMap_quotientMk`
(which gives `GeneralizingMap (Quotient.mk r)` from `hR` and `hs` alone), this shows that
`Quotient.mk r` is a generalizing spectral quotient map onto a spectral space. -/
theorem spectralSpace_quotient [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hpre : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) := by
  have : T0Space (Quotient r) := r.t0Space_quotient hR hs
  exact spectralSpace_of_isTopologicalBasis_of_surjective hB Quotient.mk_surjective
    continuous_quotient_mk' hpre

/-! ### Quotients with open projections (Scholze, Lemma 2.10) -/

/-- On a prespectral space `X`, if the first projection of the graph of `r` is open and
quasi-compact, then `Quotient.mk r` is a spectral (quasi-compact) map. When `X` is also
quasiseparated, `(r.isSpectralMap_quotientMk_of_isOpenMap hopen hqc).isLocallySpectralMap` gives
local spectrality of `Quotient.mk r`. -/
theorem isSpectralMap_quotientMk_of_isOpenMap [PrespectralSpace X]
    (hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    IsSpectralMap (Quotient.mk r) := by
  have hπ_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotientMk_of_isOpenMap hopen
  refine ⟨continuous_quotient_mk', fun V hVo hVc ↦ ?_⟩
  obtain ⟨W, hWc, rfl⟩ := hπ_open.exists_opens_image_eq_of_prespectralSpace
    continuous_quotient_mk' (by simp) hVo hVc
  exact r.isCompact_preimage_image_quotientMk hqc W.2 hWc

/-- On a quasiseparated prespectral space `X`, if the first projection of the graph of `r` is open
and quasi-compact, then `Quotient r` is quasiseparated. -/
theorem quasiSeparatedSpace_quotient_of_isOpenMap [PrespectralSpace X] [QuasiSeparatedSpace X]
    (hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    QuasiSeparatedSpace (Quotient r) := by
  have hπ_oq : IsOpenQuotientMap (Quotient.mk r) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk', r.isOpenMap_quotientMk_of_isOpenMap hopen⟩
  refine quasiSeparatedSpace_of_isTopologicalBasis_of_surjective
    (hπ_oq.isTopologicalBasis PrespectralSpace.isTopologicalBasis) Quotient.mk_surjective
    continuous_quotient_mk' ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  exact r.isCompact_preimage_image_quotientMk hqc hWo hWc

/-- On a locally spectral space `X`, if the graph of `r` is locally pro-constructible and its first
projection is open and quasi-compact, then `Quotient.mk r` lifts generalizations. -/
theorem generalizingMap_quotientMk_of_isOpenMap (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    GeneralizingMap (Quotient.mk r) :=
  r.generalizingMap_quotientMk_of_isLocallySpectralSpace hX hR hqc
    ((r.isLocallySpectralMap_fst hX hR).generalizingMap_of_isOpenMap
      (r.isLocallySpectralSpace_graph hX hR) hX hopen)

/-- **Locally spectral open-projection quotient theorem** (Scholze, *Étale cohomology of diamonds*,
Lemma 2.10). Let `X` be a quasiseparated locally spectral space and `r : Setoid X` an equivalence
relation whose graph is locally pro-constructible in `X × X` and whose first projection is open and
quasi-compact. Then `Quotient r` is locally spectral (and quasiseparated by
`Setoid.quasiSeparatedSpace_quotient_of_isOpenMap`, while `Quotient.mk r` is open, quasi-compact,
locally spectral, and generalizing). -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1))
    (hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    IsLocallySpectralSpace (Quotient r) := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
    (r.isLocallySpectralMap_fst hX hR).generalizingMap_of_isOpenMap
      (r.isLocallySpectralSpace_graph hX hR) hX hopen
  have _ : T0Space (Quotient r) := r.t0Space_quotient_of_isLocallySpectralSpace hX hR hqc hgen
  have hπ_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotientMk_of_isOpenMap hopen
  have hπ_oq : IsOpenQuotientMap (Quotient.mk r) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk', hπ_open⟩
  have hπ_qc : IsSpectralMap (Quotient.mk r) := r.isSpectralMap_quotientMk_of_isOpenMap hopen hqc
  refine isLocallySpectralSpace_iff.mpr fun q ↦ ?_
  induction q using Quotient.inductionOn with | h x => ?_
  obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
  have := hWs
  let V : Set (Quotient r) := Quotient.mk r '' W
  have hVo : IsOpen V := hπ_open W hWo
  have hVc : IsCompact V := (isCompact_iff_compactSpace.mpr hWs.toCompactSpace).image
    continuous_quotient_mk'
  let U : Set X := Quotient.mk r ⁻¹' V
  have hUo : IsOpen U := hVo.preimage continuous_quotient_mk'
  have hUc : IsCompact U := hπ_qc.isCompact_preimage_of_isOpen hVo hVc
  have _ : SpectralSpace U := spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨hUo.isOpenEmbedding_subtypeVal.isLocallySpectralSpace hX,
     isCompact_iff_compactSpace.mp hUc,
     hUo.isOpenEmbedding_subtypeVal.quasiSeparatedSpace⟩
  have _ : T0Space V := IsEmbedding.subtypeVal.t0Space
  have hg_oq : IsOpenQuotientMap (V.restrictPreimage (Quotient.mk r)) := hπ_oq.restrictPreimage V
  have hg_qc : IsSpectralMap (V.restrictPreimage (Quotient.mk r)) :=
    ((mapsTo_preimage (Quotient.mk r) V).isSpectralMap_restrict_iff
      continuous_quotient_mk'.continuousOn hVo).mpr fun K hKV hKo hKc ↦ by
      rw [inter_eq_right.mpr (preimage_mono hKV)]
      exact hπ_qc.isCompact_preimage_of_isOpen hKo hKc
  refine ⟨V, hVo, ⟨x, hxW, rfl⟩, spectralSpace_of_isTopologicalBasis_of_surjective
    (hg_oq.isTopologicalBasis PrespectralSpace.isTopologicalBasis) hg_oq.surjective
    hg_oq.continuous ?_⟩
  rintro _ ⟨O, ⟨hOo, hOc⟩, rfl⟩
  exact hg_qc.isCompact_preimage_of_isOpen (hg_oq.isOpenMap O hOo) (hOc.image hg_oq.continuous)

/-- **Spectral open-projection quotient theorem** (Scholze, *Étale cohomology of diamonds*,
Lemma 2.10, compact case). If `X` is a spectral space and `r : Setoid X` has pro-constructible graph
in `X × X` with open first projection, then `Quotient r` is a spectral space (and `Quotient.mk r` is
an open, generalizing spectral map). -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)) :
    SpectralSpace (Quotient r) := by
  have hqc : IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) := r.isSpectralMap_fst hR
  exact spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨r.isLocallySpectralSpace_quotient_of_isOpenMap SpectralSpace.isLocallySpectralSpace
       hR.isLocallyProConstructible hopen hqc,
     Quotient.compactSpace,
     r.quasiSeparatedSpace_quotient_of_isOpenMap hopen hqc⟩

end Setoid
