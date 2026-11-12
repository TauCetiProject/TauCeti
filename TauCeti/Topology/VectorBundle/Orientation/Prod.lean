/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.LinearAlgebra.Orientation.Prod
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Direct sums of oriented vector bundles

The orientation of a direct sum places the first factor before the second. The product map
from the fibre product of the two orientation covers to the orientation cover of the direct
sum is an open quotient map. Its fibres identify precisely simultaneous reversal of both
orientations.
Both signs are retained in rank zero.

The fibrewise construction and its transport law are supplied by `Orientation.prod` and
`Orientation.map_prod`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9.
-/

public section
noncomputable section

open Bundle Filter Module Set
open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℝ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] {m n : ℕ}

namespace Bundle.Trivialization

/-- Reading a product orientation in a product trivialization reads each factor orientation
in its corresponding factor trivialization. -/
theorem mapOrientation_prod (e₁ : Trivialization F₁ (π F₁ E₁)) [e₁.IsLinear ℝ]
    (e₂ : Trivialization F₂ (π F₂ E₂)) [e₂.IsLinear ℝ] {b : B}
    (hb₁ : b ∈ e₁.baseSet) (hb₂ : b ∈ e₂.baseSet)
    (o₁ : Orientation ℝ (E₁ b) (Fin m)) (o₂ : Orientation ℝ (E₂ b) (Fin n))
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    letI := VectorBundle.finiteDimensional ℝ F₁ E₁ b
    letI := VectorBundle.finiteDimensional ℝ F₂ E₂ b
    (e₁.prod e₂).mapOrientation (Fin (m + n))
      (by simpa only [prod_baseSet, mem_inter_iff] using And.intro hb₁ hb₂)
      (Orientation.prod o₁ o₂ ((VectorBundle.finrank_eq ℝ F₁ E₁ b).trans hm)
        ((VectorBundle.finrank_eq ℝ F₂ E₂ b).trans hn)) =
      Orientation.prod (e₁.mapOrientation (Fin m) hb₁ o₁)
        (e₂.mapOrientation (Fin n) hb₂ o₂) hm hn := by
  let := VectorBundle.finiteDimensional ℝ F₁ E₁ b
  let := VectorBundle.finiteDimensional ℝ F₂ E₂ b
  have hb : b ∈ (e₁.prod e₂).baseSet := by
    simpa only [prod_baseSet, mem_inter_iff] using And.intro hb₁ hb₂
  have he : (e₁.prod e₂).linearEquivAt ℝ b hb =
      (e₁.linearEquivAt ℝ b hb₁).prodCongr (e₂.linearEquivAt ℝ b hb₂) := by
    exact congrArg ContinuousLinearEquiv.toLinearEquiv (continuousLinearEquivAt_prod (𝕜 := ℝ) hb)
  simp only [mapOrientation_apply, he, Orientation.map_prod]

end Bundle.Trivialization

namespace TauCeti.VectorBundleOrientation

/-- The orientation of the fibrewise direct sum, ordered with `E₁` before `E₂`. -/
def prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n))
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    VectorBundleOrientation (F₁ × F₂) (E₁ ×ᵇ E₂) (Fin (m + n)) := by
  letI := fun b ↦ VectorBundle.finiteDimensional ℝ F₁ E₁ b
  letI := fun b ↦ VectorBundle.finiteDimensional ℝ F₂ E₂ b
  exact ofEventually (by simp [Module.finrank_prod, hm, hn])
    (fun b ↦ Orientation.prod (o₁ b) (o₂ b)
      ((VectorBundle.finrank_eq ℝ F₁ E₁ b).trans hm)
      ((VectorBundle.finrank_eq ℝ F₂ E₂ b).trans hn))
    (fun b ↦ (trivializationAt F₁ E₁ b).prod (trivializationAt F₂ E₂ b))
    (fun b ↦ ⟨FiberBundle.mem_baseSet_trivializationAt' b,
      FiberBundle.mem_baseSet_trivializationAt' b⟩)
    (fun b ↦ by
      filter_upwards [o₁.eventually_mapOrientation_eq' b, o₂.eventually_mapOrientation_eq' b]
        with x hx₁ hx₂ hx
      have hxmem : x ∈ (trivializationAt F₁ E₁ b).baseSet ∧
          x ∈ (trivializationAt F₂ E₂ b).baseSet := by
        simpa only [Trivialization.prod_baseSet, mem_inter_iff] using hx
      rw [Trivialization.mapOrientation_prod _ _ hxmem.1 hxmem.2 _ _ hm hn,
        Trivialization.mapOrientation_prod _ _
          (FiberBundle.mem_baseSet_trivializationAt' b)
          (FiberBundle.mem_baseSet_trivializationAt' b) _ _ hm hn]
      exact congrArg₂ (fun a c ↦ Orientation.prod a c hm hn) (hx₁ hxmem.1) (hx₂ hxmem.2))

@[simp]
theorem prod_apply (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n))
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) (b : B) :
    letI := VectorBundle.finiteDimensional ℝ F₁ E₁ b
    letI := VectorBundle.finiteDimensional ℝ F₂ E₂ b
    prod o₁ o₂ hm hn b = Orientation.prod (o₁ b) (o₂ b)
      ((VectorBundle.finrank_eq ℝ F₁ E₁ b).trans hm)
      ((VectorBundle.finrank_eq ℝ F₂ E₂ b).trans hn) :=
  by
    unfold prod
    exact congrFun (coe_ofEventually _ _ _ _ _) b

/-- Reversing the first bundle orientation reverses the direct-sum orientation. -/
@[simp]
theorem prod_neg_left (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n))
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    prod (-o₁) o₂ hm hn = -prod o₁ o₂ hm hn := by
  ext b
  simp

/-- Reversing the second bundle orientation reverses the direct-sum orientation. -/
@[simp]
theorem prod_neg_right (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n))
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    prod o₁ (-o₂) hm hn = -prod o₁ o₂ hm hn := by
  ext b
  simp

end TauCeti.VectorBundleOrientation

namespace TauCeti.VectorBundleOrientationCover

/-- The fibre product of two orientation covers, with the topology induced from their product.
Its points are pairs of orientations over the same base point. -/
abbrev FiberProd (F₁ : Type*) (E₁ : B → Type*) [∀ b, AddCommMonoid (E₁ b)]
    [∀ b, Module ℝ (E₁ b)] (F₂ : Type*) (E₂ : B → Type*) [∀ b, AddCommMonoid (E₂ b)]
    [∀ b, Module ℝ (E₂ b)] (m n : ℕ) :=
  {p : VectorBundleOrientationCover F₁ E₁ (Fin m) ×
      VectorBundleOrientationCover F₂ E₂ (Fin n) // p.1.proj = p.2.proj}

/-- The direct-sum comparison sends a pair of fibre orientations to their ordered product. -/
def prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p : FiberProd F₁ E₁ F₂ E₂ m n) :
    VectorBundleOrientationCover (F₁ × F₂) (E₁ ×ᵇ E₂) (Fin (m + n)) := by
  letI := fun b ↦ VectorBundle.finiteDimensional ℝ F₁ E₁ b
  letI := fun b ↦ VectorBundle.finiteDimensional ℝ F₂ E₂ b
  exact ⟨p.1.1.proj, Orientation.prod p.1.1.orientation (p.2.symm ▸ p.1.2.orientation)
    ((VectorBundle.finrank_eq ℝ F₁ E₁ p.1.1.proj).trans hm)
    ((VectorBundle.finrank_eq ℝ F₂ E₂ p.1.1.proj).trans hn)⟩

/-- On two orientations over a common base point, the comparison is their actual linear
product orientation. The finite-dimensional fibre instances are inherited from the bundle. -/
@[simp]
theorem prodMap_mk (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) (b : B)
    (o₁ : Orientation ℝ (E₁ b) (Fin m)) (o₂ : Orientation ℝ (E₂ b) (Fin n)) :
    letI := VectorBundle.finiteDimensional ℝ F₁ E₁ b
    letI := VectorBundle.finiteDimensional ℝ F₂ E₂ b
    prodMap hm hn ⟨(⟨b, o₁⟩, ⟨b, o₂⟩), rfl⟩ =
      ⟨b, Orientation.prod o₁ o₂ ((VectorBundle.finrank_eq ℝ F₁ E₁ b).trans hm)
        ((VectorBundle.finrank_eq ℝ F₂ E₂ b).trans hn)⟩ :=
  (rfl)

@[simp]
theorem proj_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p : FiberProd F₁ E₁ F₂ E₂ m n) : (prodMap hm hn p).proj = p.1.1.proj :=
  (rfl)

private theorem preimage_sheet_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (e₁ : Trivialization F₁ (π F₁ E₁)) [e₁.IsLinear ℝ]
    (e₂ : Trivialization F₂ (π F₂ E₂)) [e₂.IsLinear ℝ]
    (o₁ : Orientation ℝ F₁ (Fin m)) (o₂ : Orientation ℝ F₂ (Fin n)) :
    {p : FiberProd F₁ E₁ F₂ E₂ m n |
      p.1.1 ∈ sheet e₁ o₁ ∧ p.1.2 ∈ sheet e₂ o₂} ⊆
      prodMap hm hn ⁻¹' sheet (e₁.prod e₂) (Orientation.prod o₁ o₂ hm hn) := by
  rintro ⟨⟨⟨b, p⟩, ⟨b', q⟩⟩, h⟩ ⟨hp, hq⟩
  obtain ⟨hp, hpo⟩ := mem_sheet_iff.1 hp
  obtain ⟨hq, hqo⟩ := mem_sheet_iff.1 hq
  cases h
  simp only [mem_preimage, prodMap_mk]
  exact mem_sheet_iff.2 ⟨⟨hp, hq⟩, by
    rw [Trivialization.mapOrientation_prod _ _ hp hq _ _ hm hn, hpo, hqo]⟩

/-- The direct-sum comparison of orientation covers is continuous. -/
theorem continuous_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    Continuous (prodMap (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) hm hn) := by
  refine continuous_of_isOpen_preimage_sheet (by
    simpa only [Function.comp_def, proj_prodMap] using
      (continuous_proj.comp (continuous_fst.comp continuous_subtype_val) :
        Continuous fun p : FiberProd F₁ E₁ F₂ E₂ m n ↦ p.1.1.proj)) fun b o ↦ ?_
  refine isOpen_iff_forall_mem_open.2 fun p hp ↦ ?_
  obtain ⟨hb, ho⟩ := mem_sheet_iff.1 hp
  let e₁ := trivializationAt F₁ E₁ b
  let e₂ := trivializationAt F₂ E₂ b
  have hb₁ : p.1.1.proj ∈ e₁.baseSet := hb.1
  have hb₂ : p.1.2.proj ∈ e₂.baseSet := p.2 ▸ hb.2
  let o₁ := e₁.mapOrientation (Fin m) hb₁ p.1.1.orientation
  let o₂ := e₂.mapOrientation (Fin n) hb₂ p.1.2.orientation
  have hopen : IsOpen {q : FiberProd F₁ E₁ F₂ E₂ m n |
      q.1.1 ∈ sheet e₁ o₁ ∧ q.1.2 ∈ sheet e₂ o₂} :=
    ((isOpen_sheet (by simpa only [Fintype.card_fin] using hm.symm) e₁ o₁).preimage
      (continuous_fst.comp continuous_subtype_val)).inter
      ((isOpen_sheet (by simpa only [Fintype.card_fin] using hn.symm) e₂ o₂).preimage
        (continuous_snd.comp continuous_subtype_val))
  refine ⟨_, ?_, hopen, mem_sheet_iff.2 ⟨hb₁, rfl⟩, mem_sheet_iff.2 ⟨hb₂, rfl⟩⟩
  have hmodel : Orientation.prod o₁ o₂ hm hn = o := by
    rcases p with ⟨⟨⟨x, a⟩, ⟨y, c⟩⟩, hxy⟩
    cases hxy
    simp only [prodMap] at ho
    exact (Trivialization.mapOrientation_prod e₁ e₂ hb₁ hb₂ a c hm hn).symm.trans ho
  exact (preimage_sheet_prodMap hm hn e₁ e₂ o₁ o₂).trans (by rw [hmodel]; exact Subset.rfl)


omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] in
/-- Simultaneous reversal of the two orientations in the fibre product. -/
def prodDeck : FiberProd F₁ E₁ F₂ E₂ m n ≃ₜ FiberProd F₁ E₁ F₂ E₂ m n :=
  (deck.prodCongr deck).subtype (fun p ↦ by simp)

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] in
@[simp]
theorem prodDeck_val (p : FiberProd F₁ E₁ F₂ E₂ m n) :
    (prodDeck p).val = (deck p.1.1, deck p.1.2) := by
  rcases p with ⟨⟨p, q⟩, h⟩
  simp [prodDeck]

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] in
@[simp]
theorem prodDeck_symm :
    (prodDeck : FiberProd F₁ E₁ F₂ E₂ m n ≃ₜ _).symm = prodDeck := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  simp [prodDeck]

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] in
@[simp]
theorem prodDeck_prodDeck (p : FiberProd F₁ E₁ F₂ E₂ m n) : prodDeck (prodDeck p) = p := by
  simpa only [prodDeck_symm] using
    (prodDeck : FiberProd F₁ E₁ F₂ E₂ m n ≃ₜ _).symm_apply_apply p

/-- Reversing both factor orientations preserves their direct-sum orientation. -/
@[simp]
theorem prodMap_prodDeck (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p : FiberProd F₁ E₁ F₂ E₂ m n) : prodMap hm hn (prodDeck p) = prodMap hm hn p := by
  let := fun b ↦ VectorBundle.finiteDimensional ℝ F₁ E₁ b
  let := fun b ↦ VectorBundle.finiteDimensional ℝ F₂ E₂ b
  rcases p with ⟨⟨⟨b, o₁⟩, ⟨b', o₂⟩⟩, h⟩
  cases h
  have hdeck : prodDeck ⟨(⟨b, o₁⟩, ⟨b, o₂⟩), rfl⟩ =
      (⟨(⟨b, -o₁⟩, ⟨b, -o₂⟩), rfl⟩ : FiberProd F₁ E₁ F₂ E₂ m n) := by
    apply Subtype.ext
    simp [deck_apply]
  rw [hdeck, prodMap_mk, prodMap_mk, Orientation.prod_neg_neg]

/-- The direct-sum comparison identifies exactly simultaneous reversal of both orientations. -/
theorem prodMap_eq_prodMap_iff (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p q : FiberProd F₁ E₁ F₂ E₂ m n) :
    prodMap hm hn p = prodMap hm hn q ↔ p = q ∨ p = prodDeck q := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hbase : p.1.1.proj = q.1.1.proj := by
      simpa only [proj_prodMap] using congrArg proj h
    have hbase' : p.1.2.proj = q.1.2.proj := p.2.symm.trans (hbase.trans q.2)
    rcases eq_or_eq_deck (by simpa only [Fintype.card_fin] using hm.symm) hbase with h₁ | h₁ <;>
      rcases eq_or_eq_deck (by simpa only [Fintype.card_fin] using hn.symm) hbase' with h₂ | h₂
    · exact .inl (Subtype.ext (Prod.ext h₁ h₂))
    · exfalso
      rcases q with ⟨⟨⟨b, a⟩, ⟨b', c⟩⟩, hq⟩
      cases hq
      have hp : p = ⟨(⟨b, a⟩, ⟨b, -c⟩), rfl⟩ := by
        apply Subtype.ext
        exact Prod.ext h₁ (h₂.trans (deck_apply _))
      simp only [hp, prodMap_mk, Orientation.prod_neg_right] at h
      exact Module.Ray.ne_neg_self _ (mk_eq_mk_iff.1 h).symm
    · exfalso
      rcases q with ⟨⟨⟨b, a⟩, ⟨b', c⟩⟩, hq⟩
      cases hq
      have hp : p = ⟨(⟨b, -a⟩, ⟨b, c⟩), rfl⟩ := by
        apply Subtype.ext
        exact Prod.ext (h₁.trans (deck_apply _)) h₂
      simp only [hp, prodMap_mk, Orientation.prod_neg_left] at h
      exact Module.Ray.ne_neg_self _ (mk_eq_mk_iff.1 h).symm
    · exact .inr (Subtype.ext ((Prod.ext h₁ h₂).trans (prodDeck_val q).symm))
  · rintro (rfl | rfl)
    · rfl
    · exact prodMap_prodDeck hm hn q

/-- Every orientation of a direct-sum fibre is the product of two factor orientations. -/
theorem surjective_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    Function.Surjective (prodMap (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) hm hn) := by
  intro p
  obtain ⟨a, ha⟩ := surjective_proj (F := F₁) (E := E₁) (ι := Fin m)
    (by simpa only [Fintype.card_fin] using hm.symm) p.proj
  obtain ⟨c, hc⟩ := surjective_proj (F := F₂) (E := E₂) (ι := Fin n)
    (by simpa only [Fintype.card_fin] using hn.symm) p.proj
  let q : FiberProd F₁ E₁ F₂ E₂ m n := ⟨(a, c), ha.trans hc.symm⟩
  rcases eq_or_eq_deck (by simp [Module.finrank_prod, hm, hn])
    (p := prodMap hm hn q) (q := p) (by simpa only [proj_prodMap] using ha.symm) with h | h
  · exact ⟨q, h.symm⟩
  · rcases a with ⟨b, a⟩
    rcases c with ⟨b', c⟩
    obtain rfl : b = b' := ha.trans hc.symm
    refine ⟨⟨(⟨b, -a⟩, ⟨b, c⟩), rfl⟩, ?_⟩
    simpa only [q, prodMap_mk, deck_apply, Orientation.prod_neg_left] using h.symm


/-- The direct-sum comparison is open: locally it is the identity on the common base. -/
theorem isOpenMap_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    IsOpenMap (prodMap (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) hm hn) := by
  intro U hU
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨p, hp, rfl⟩
  rcases p with ⟨⟨⟨b, a⟩, ⟨b', c⟩⟩, h⟩
  cases h
  let e₁ := trivializationAt F₁ E₁ b
  let e₂ := trivializationAt F₂ E₂ b
  have hb₁ : b ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb₂ : b ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  let V := e₁.baseSet ∩ e₂.baseSet
  have hV : IsOpen V := e₁.open_baseSet.inter e₂.open_baseSet
  let o₁ := e₁.mapOrientation (Fin m) hb₁ a
  let o₂ := e₂.mapOrientation (Fin n) hb₂ c
  let s : V → FiberProd F₁ E₁ F₂ E₂ m n := fun x ↦
    ⟨(⟨x, (e₁.mapOrientation (Fin m) x.2.1).symm o₁⟩,
      ⟨x, (e₂.mapOrientation (Fin n) x.2.2).symm o₂⟩), rfl⟩
  have hs : Continuous s := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact (continuous_mk_mapOrientation_symm
        (by simpa only [Fintype.card_fin] using hm.symm) e₁ o₁).comp
        (continuous_subtype_val.subtype_mk fun x ↦ x.2.1)
    · exact (continuous_mk_mapOrientation_symm
        (by simpa only [Fintype.card_fin] using hn.symm) e₂ o₂).comp
        (continuous_subtype_val.subtype_mk fun x ↦ x.2.2)
  let t := prodMap hm hn ∘ s
  have ht : Continuous t := (continuous_prodMap hm hn).comp hs
  have hpt : proj ∘ t = (Subtype.val : V → B) := by
    funext x
    simp only [t, Function.comp_apply, proj_prodMap]
    rfl
  have htopen : Topology.IsOpenEmbedding t :=
    (isCoveringMap_proj (F := F₁ × F₂) (E := E₁ ×ᵇ E₂)
      (by simp [Module.finrank_prod, hm, hn])).isLocalHomeomorph.isOpenEmbedding_of_comp
      (hpt.symm ▸ hV.isOpenEmbedding_subtypeVal) ht
  have hsb : s ⟨b, hb₁, hb₂⟩ = ⟨(⟨b, a⟩, ⟨b, c⟩), rfl⟩ := by
    simp [s, o₁, o₂]
  refine ⟨t '' (s ⁻¹' U), ?_, htopen.isOpenMap _ (hU.preimage hs), ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨s x, hx, rfl⟩
  · exact ⟨⟨b, hb₁, hb₂⟩, by simpa only [mem_preimage, hsb] using hp,
      congrArg (prodMap hm hn) hsb⟩

/-- The direct-sum orientation cover has the quotient topology for simultaneous reversal. -/
theorem isQuotientMap_prodMap (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    Topology.IsQuotientMap (prodMap (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) hm hn) :=
  (isOpenMap_prodMap hm hn).isQuotientMap (continuous_prodMap hm hn) (surjective_prodMap hm hn)

/-- The orientation cover of the direct sum is the quotient of the fibre product of the factor
covers. By `prodMap_eq_prodMap_iff`, its equivalence classes are simultaneous deck orbits. -/
def prodQuotientHomeomorph (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n) :
    Quotient (Setoid.ker (prodMap (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) hm hn)) ≃ₜ
      VectorBundleOrientationCover (F₁ × F₂) (E₁ ×ᵇ E₂) (Fin (m + n)) :=
  (isQuotientMap_prodMap hm hn).homeomorph (f := ⟨_, continuous_prodMap hm hn⟩)

@[simp]
theorem prodQuotientHomeomorph_mk (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p : FiberProd F₁ E₁ F₂ E₂ m n) :
    prodQuotientHomeomorph hm hn (Quotient.mk _ p) = prodMap hm hn p :=
  (rfl)

/-- The quotient class of a pair is recovered from its direct-sum orientation. This form also
allows simplification after the forward comparison has evaluated on a representative. -/
@[simp]
theorem prodQuotientHomeomorph_symm_prodMap
    (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (p : FiberProd F₁ E₁ F₂ E₂ m n) :
    (prodQuotientHomeomorph hm hn).symm (prodMap hm hn p) = Quotient.mk _ p := by
  rw [← prodQuotientHomeomorph_mk hm hn p]
  exact (prodQuotientHomeomorph hm hn).symm_apply_apply _

end TauCeti.VectorBundleOrientationCover
