/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper homotopies and proper homotopy equivalences

A homotopy `F : f₀ ≃ f₁` is *proper* when its underlying map `I × X → Y` on the whole cylinder is
proper (`IsProperMap F`). Each slice `F.curry t` — in particular both endpoints `f₀` and `f₁` — is
then proper, and properness is preserved by constant homotopies, reversal, concatenation, and
horizontal composition.

A continuous map `f : X → Y` is a *proper homotopy equivalence*
(`ContinuousMap.HasProperHomotopyInverse`) if it is proper and has a proper homotopy inverse
`g : Y → X` for which both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` are proper on `I × X` and
`I × Y`. These are the equivalences of the proper homotopy category, in which invariants at
infinity such as ends and simple connectivity at infinity live. Proper homotopy equivalences
contain homeomorphisms (`Homeomorph.hasProperHomotopyInverse`), are closed under composition
(`ContinuousMap.HasProperHomotopyInverse.comp`) and inverse selection
(`ContinuousMap.HasProperHomotopyInverse.exists_symm`), and are invariant under proper homotopy
(`ContinuousMap.HasProperHomotopyInverse.iff_of_homotopy`). No separation or local compactness
assumption is required.

## Main declarations

* `ContinuousMap.Homotopy.isProperMap_curry`, `ContinuousMap.Homotopy.isProperMap_refl_iff`,
  `ContinuousMap.Homotopy.isProperMap_symm_iff`, `ContinuousMap.Homotopy.isProperMap_trans_iff`,
  `ContinuousMap.Homotopy.isProperMap_comp`: closure of proper homotopies under slicing, constant
  homotopies, reversal, concatenation, and horizontal composition, with relative counterparts in
  `ContinuousMap.HomotopyRel`.
* `ContinuousMap.HasProperHomotopyInverse`: proper homotopy equivalences, with `id`, `exists_symm`,
  `comp`, `of_homotopy`, `iff_of_homotopy`, and `of_deformationRetraction`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1.
-/

public section

open Set TauCeti
open scoped unitInterval

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Homotopy

section Basic

variable {f₀ f₁ f₂ g₀ g₁ : C(X, Y)}

/-- Every time slice `F.curry t` of a proper homotopy `F : I × X → Y` is proper. -/
theorem isProperMap_curry (F : Homotopy f₀ f₁) (hF : IsProperMap F) (t : I) :
    IsProperMap (F.curry t) := by
  have h : (F.curry t : X → Y) = F ∘ Prod.mk t := by ext x; simp
  rw [h]
  exact hF.comp (isProperMap_prodMk_left t)

/-- The initial map of a proper homotopy is proper. -/
theorem isProperMap_left (F : Homotopy f₀ f₁) (hF : IsProperMap F) : IsProperMap f₀ := by
  simpa using F.isProperMap_curry hF 0

/-- The terminal map of a proper homotopy is proper. -/
theorem isProperMap_right (F : Homotopy f₀ f₁) (hF : IsProperMap F) : IsProperMap f₁ := by
  simpa using F.isProperMap_curry hF 1

/-- The constant homotopy on `f` is proper if and only if `f` is proper. -/
@[simp]
theorem isProperMap_refl_iff {f : C(X, Y)} : IsProperMap (Homotopy.refl f) ↔ IsProperMap f := by
  refine ⟨(Homotopy.refl f).isProperMap_left, fun hf ↦ ?_⟩
  have h : (Homotopy.refl f : I × X → Y) = f ∘ Prod.snd := by ext ⟨t, x⟩; simp
  rw [h]
  exact hf.comp isProperMap_snd_of_compactSpace

/-- Reversing a homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_symm_iff {F : Homotopy f₀ f₁} : IsProperMap F.symm ↔ IsProperMap F := by
  let e : I × X ≃ₜ I × X := unitInterval.symmHomeomorph.prodCongr (.refl X)
  have h : (F.symm : I × X → Y) = F ∘ e := by ext ⟨t, x⟩; simp [e]
  rw [h]
  exact e.comp_isProperMap_iff'

/-- Reversing a proper homotopy gives a proper homotopy. -/
theorem isProperMap_symm {F : Homotopy f₀ f₁} (hF : IsProperMap F) : IsProperMap F.symm :=
  isProperMap_symm_iff.2 hF

/-- Casting endpoint equalities on a homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_cast_iff {F : Homotopy f₀ f₁} (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    IsProperMap (F.cast h₀ h₁) ↔ IsProperMap F := by
  have h : (F.cast h₀ h₁ : I × X → Y) = F := by ext ⟨t, x⟩; simp
  rw [h]

/-- Homeomorphism of `I × X` onto the lower half `{p | p.1 ≤ 1 / 2}` of the cylinder. -/
@[simps!]
private noncomputable def leftHalfHomeomorph (X : Type*) [TopologicalSpace X] :
    I × X ≃ₜ {p : I × X // (p.1 : ℝ) ≤ 1 / 2} where
  toFun q := ⟨(⟨(q.1 : ℝ) / 2, by constructor <;> linarith [q.1.property.1, q.1.property.2]⟩, q.2),
    by dsimp; linarith [q.1.property.2]⟩
  invFun p :=
    (⟨2 * (p.val.1 : ℝ), by constructor <;> linarith [p.val.1.property.1, p.property]⟩, p.val.2)
  left_inv q := by
    ext
    · dsimp; ring
    · rfl
  right_inv p := by
    ext
    · dsimp; ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The concatenation `F.trans G` is proper if and only if both `F` and `G` are proper. -/
@[simp]
theorem isProperMap_trans_iff {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂} :
    IsProperMap (F.trans G) ↔ IsProperMap F ∧ IsProperMap G := by
  let s : Set (I × X) := {p | (p.1 : ℝ) ≤ 1 / 2}
  let t : Set (I × X) := {p | 1 / 2 ≤ (p.1 : ℝ)}
  have hs : IsClosed s := isClosed_le (by fun_prop) continuous_const
  have ht : IsClosed t := isClosed_le continuous_const (by fun_prop)
  have hst : s ∪ t = univ := by ext p; exact ⟨fun _ ↦ trivial, fun _ ↦ le_total (p.1 : ℝ) (1 / 2)⟩
  have hleft : ∀ {g₀ g₁ g₂ : C(X, Y)} (F' : Homotopy g₀ g₁) (G' : Homotopy g₁ g₂),
      IsProperMap (s.domRestrict (F'.trans G')) ↔ IsProperMap F' := by
    intro g₀ g₁ g₂ F' G'
    rw [← (leftHalfHomeomorph X).comp_isProperMap_iff']
    have hcomp : s.domRestrict (F'.trans G') ∘ leftHalfHomeomorph X = F' := by
      ext ⟨u, x⟩
      have hu : ((u : ℝ) / 2) ≤ 1 / 2 := by linarith [u.property.2]
      simp only [Function.comp_apply, domRestrict_apply, leftHalfHomeomorph_apply_coe, trans_apply,
        dite_eq_left hu]
      congr 1
      ext
      · dsimp; ring
      · rfl
    rw [hcomp]
  rw [hs.isProperMap_iff_domRestrict_of_union_eq_univ ht hst, hleft F G]
  -- Transfer the upper half `{p | 1 / 2 ≤ p.1}` to the lower half via interval reversal.
  let e : s ≃ₜ t := (unitInterval.symmHomeomorph.prodCongr (.refl X)).subtype fun ⟨u, x⟩ ↦ by
    simp only [s, t, mem_ofPred_eq, Homeomorph.coe_prodCongr, Prod.map_apply,
      unitInterval.symmHomeomorph_apply, unitInterval.coe_symm_eq]
    constructor <;> intro h <;> linarith
  have hright : t.domRestrict (F.trans G) ∘ e = s.domRestrict (G.symm.trans F.symm) := by
    ext ⟨⟨u, x⟩, hu⟩
    have hsymm := congrFun (congrArg DFunLike.coe (Homotopy.symm_trans F G)) (u, x)
    simpa [e, Homotopy.symm_apply] using hsymm
  rw [← e.comp_isProperMap_iff', hright, hleft G.symm F.symm, isProperMap_symm_iff]

/-- Concatenating two proper homotopies gives a proper homotopy. -/
theorem isProperMap_trans {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : IsProperMap F) (hG : IsProperMap G) : IsProperMap (F.trans G) :=
  isProperMap_trans_iff.2 ⟨hF, hG⟩

end Basic

section Comp

/-- Horizontal composition of proper homotopies is proper. -/
theorem isProperMap_comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁}
    {F : Homotopy f₀ f₁} (hG : IsProperMap G) (hF : IsProperMap F) :
    IsProperMap (G.comp F) := by
  have h : (G.comp F : I × X → Z) =
      G ∘ Prod.map id F ∘ Homeomorph.prodAssoc I I X ∘ Prod.map (fun t : I ↦ (t, t)) id := by
    ext ⟨t, x⟩
    simp [Homeomorph.prodAssoc]
  rw [h]
  exact hG.comp ((isProperMap_id.prodMap hF).comp
    ((Homeomorph.prodAssoc I I X).isProperMap.comp
      ((continuous_id.prodMk continuous_id).isProperMap.prodMap isProperMap_id)))

/-- Precomposing a proper homotopy with a proper continuous map gives a proper homotopy. -/
theorem isProperMap_compContinuousMap {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁} {f : C(X, Y)}
    (hG : IsProperMap G) (hf : IsProperMap f) : IsProperMap (G.compContinuousMap f) := by
  have h : (G.compContinuousMap f : I × X → Z) = G.comp (Homotopy.refl f) := by
    ext ⟨t, x⟩
    simp
  rw [h]
  exact isProperMap_comp hG (isProperMap_refl_iff.2 hf)

end Comp

end Homotopy

namespace HomotopyRel

variable {f₀ f₁ f₂ g₀ g₁ : C(X, Y)} {S : Set X}

/-- The constant relative homotopy on `f` is proper if and only if `f` is proper. -/
@[simp]
theorem isProperMap_refl_iff {f : C(X, Y)} :
    IsProperMap (HomotopyRel.refl f S) ↔ IsProperMap f := by
  have h : (HomotopyRel.refl f S : I × X → Y) = Homotopy.refl f := by ext ⟨t, x⟩; simp
  rw [h]
  exact Homotopy.isProperMap_refl_iff

/-- Reversing a relative homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_symm_iff {F : HomotopyRel f₀ f₁ S} : IsProperMap F.symm ↔ IsProperMap F := by
  have h : (F.symm : I × X → Y) = F.toHomotopy.symm := by ext ⟨t, x⟩; simp
  rw [h, Homotopy.isProperMap_symm_iff, HomotopyWith.coe_toHomotopy]

/-- Casting endpoint equalities on a relative homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_cast_iff {F : HomotopyRel f₀ f₁ S} (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    IsProperMap (F.cast h₀ h₁) ↔ IsProperMap F := by
  have h : (F.cast h₀ h₁ : I × X → Y) = F := by ext ⟨t, x⟩; simp
  rw [h]

/-- Concatenating two relative homotopies is proper if and only if both factors are proper. -/
@[simp]
theorem isProperMap_trans_iff {F : HomotopyRel f₀ f₁ S} {G : HomotopyRel f₁ f₂ S} :
    IsProperMap (F.trans G) ↔ IsProperMap F ∧ IsProperMap G := by
  have h : (F.trans G : I × X → Y) = F.toHomotopy.trans G.toHomotopy := by
    ext ⟨t, x⟩
    simp only [HomotopyRel.trans_apply, Homotopy.trans_apply, HomotopyWith.coe_toHomotopy]
  rw [h, Homotopy.isProperMap_trans_iff, HomotopyWith.coe_toHomotopy, HomotopyWith.coe_toHomotopy]

/-- Postcomposing a proper relative homotopy with a proper continuous map gives a proper relative
homotopy. -/
theorem isProperMap_compContinuousMap {F : f₀.HomotopyRel f₁ S} {g : C(Y, Z)}
    (hF : IsProperMap F) (hg : IsProperMap g) : IsProperMap (F.compContinuousMap g) := by
  have h : (F.compContinuousMap g : I × X → Z) = (Homotopy.refl g).comp F.toHomotopy := by
    ext ⟨t, x⟩
    simp
  rw [h]
  exact Homotopy.isProperMap_comp (Homotopy.isProperMap_refl_iff.2 hg)
    (by rwa [HomotopyWith.coe_toHomotopy])

end HomotopyRel

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

namespace HasProperHomotopyInverse

/-- A proper map with a proper inverse `g` up to proper homotopies `g ∘ f ≃ id` and
`f ∘ g ≃ id` is a proper homotopy equivalence. -/
theorem intro {f : C(X, Y)} (hf : IsProperMap f) (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : f.HasProperHomotopyInverse :=
  ⟨hf, g, hg, H, H', hH, hH'⟩

/-- A proper homotopy equivalence is a proper map. -/
theorem isProperMap {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) : IsProperMap f :=
  hf.1

/-- A proper homotopy equivalence has a proper homotopy inverse `g`, with proper homotopies
`g ∘ f ≃ id` and `f ∘ g ≃ id`. -/
theorem exists_inverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), IsProperMap g ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' :=
  hf.2

/-- A proper homotopy equivalence `f` is a homotopy equivalence: forgetting properness gives a
homotopy equivalence whose forward map is `f`. -/
theorem exists_homotopyEquiv {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ e : X ≃ₕ Y, (e : X → Y) = f := by
  obtain ⟨g, -, H, H', -, -⟩ := hf.exists_inverse
  exact ⟨⟨f, g, ⟨H⟩, ⟨H'⟩⟩, rfl⟩

/-- Every proper homotopy equivalence admits a proper homotopy inverse which is itself a proper
homotopy equivalence. -/
theorem exists_symm {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), g.HasProperHomotopyInverse ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  exact ⟨g, .intro hg f hf.isProperMap H' H hH' hH, H, H', hH, hH'⟩

/-- **Proper homotopy equivalences compose.** -/
theorem comp {f : C(X, Y)} {g : C(Y, Z)} (hg : g.HasProperHomotopyInverse)
    (hf : f.HasProperHomotopyInverse) : (g.comp f).HasProperHomotopyInverse := by
  obtain ⟨f', hf', Hf, Hf', hHf, hHf'⟩ := hf.exists_inverse
  obtain ⟨g', hg', Hg, Hg', hHg, hHg'⟩ := hg.exists_inverse
  let L₁ : Homotopy ((f'.comp g').comp (g.comp f)) (f'.comp f) :=
    ((Homotopy.refl f').comp (Hg.compContinuousMap f)).cast
      (by ext; simp) (by ext; simp)
  let R₁ : Homotopy ((g.comp f).comp (f'.comp g')) (g.comp g') :=
    ((Homotopy.refl g).comp (Hf'.compContinuousMap g')).cast
      (by ext; simp) (by ext; simp)
  have hL₁ : IsProperMap L₁ := by
    dsimp only [L₁]
    rw [Homotopy.isProperMap_cast_iff]
    exact Homotopy.isProperMap_comp (Homotopy.isProperMap_refl_iff.2 hf')
      (Homotopy.isProperMap_compContinuousMap hHg hf.isProperMap)
  have hR₁ : IsProperMap R₁ := by
    dsimp only [R₁]
    rw [Homotopy.isProperMap_cast_iff]
    exact Homotopy.isProperMap_comp (Homotopy.isProperMap_refl_iff.2 hg.isProperMap)
      (Homotopy.isProperMap_compContinuousMap hHf' hg')
  exact .intro (hg.isProperMap.comp hf.isProperMap) (f'.comp g') (hf'.comp hg')
    (L₁.trans Hf) (R₁.trans Hg') (Homotopy.isProperMap_trans hL₁ hHf)
    (Homotopy.isProperMap_trans hR₁ hHg')

/-- Proper homotopy equivalence transports along a proper homotopy `F : f ≃ f'`. -/
theorem of_homotopy {f f' : C(X, Y)} (hf : f.HasProperHomotopyInverse) (F : Homotopy f f')
    (hF : IsProperMap F) : f'.HasProperHomotopyInverse := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  exact .intro (F.isProperMap_right hF) g hg
    (((Homotopy.refl g).comp F.symm).trans H)
    ((F.symm.compContinuousMap g).trans H')
    (Homotopy.isProperMap_trans
      (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl_iff.2 hg)
        (Homotopy.isProperMap_symm hF)) hH)
    (Homotopy.isProperMap_trans
      (Homotopy.isProperMap_compContinuousMap (Homotopy.isProperMap_symm hF) hg) hH')

/-- Two properly homotopic maps are proper homotopy equivalences simultaneously. -/
theorem iff_of_homotopy {f f' : C(X, Y)} (F : Homotopy f f') (hF : IsProperMap F) :
    f.HasProperHomotopyInverse ↔ f'.HasProperHomotopyInverse :=
  ⟨fun hf ↦ hf.of_homotopy F hF,
    fun hf' ↦ hf'.of_homotopy F.symm (Homotopy.isProperMap_symm hF)⟩

/-- **A proper deformation retraction gives a proper homotopy equivalence.** If `i : C(Y, X)`
admits a left inverse `r : C(X, Y)` together with a proper homotopy `K` from `i.comp r` to `id_X`,
then both `i` and `r` are automatically proper and `i` has a proper homotopy inverse. -/
theorem of_deformationRetraction {i : C(Y, X)} {r : C(X, Y)} (hri : Function.LeftInverse r i)
    {K : (i.comp r).Homotopy (ContinuousMap.id X)} (hK : IsProperMap K) :
    i.HasProperHomotopyInverse := by
  have hir : IsProperMap (i ∘ r) := by
    rw [← ContinuousMap.coe_comp]
    exact K.isProperMap_left hK
  have hrp : IsProperMap r :=
    isProperMap_of_comp_of_inj r.continuous i.continuous hir hri.injective
  have hi : IsProperMap i :=
    isProperMap_of_comp_of_surj r.continuous i.continuous hir hri.surjective
  refine .intro hi r hrp
    ((Homotopy.refl (ContinuousMap.id Y)).cast (ContinuousMap.ext fun y ↦ (hri y).symm) rfl) K
    ?_ hK
  rw [Homotopy.isProperMap_cast_iff, Homotopy.isProperMap_refl_iff]
  exact isProperMap_id

end HasProperHomotopyInverse

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse :=
  ContinuousMap.HasProperHomotopyInverse.of_deformationRetraction (r := e.symm)
    (fun x ↦ by simp)
    (K := (ContinuousMap.Homotopy.refl (ContinuousMap.id Y)).cast
      e.toContinuousMap_comp_symm.symm rfl)
    (by simp [isProperMap_id])

/-- The identity map is a proper homotopy equivalence. -/
theorem ContinuousMap.HasProperHomotopyInverse.id (X : Type*) [TopologicalSpace X] :
    (ContinuousMap.id X).HasProperHomotopyInverse := by
  simpa using (Homeomorph.refl X).hasProperHomotopyInverse
