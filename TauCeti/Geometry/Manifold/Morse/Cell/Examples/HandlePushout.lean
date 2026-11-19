/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.HandlePushout
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Handle attachments in examples

Milnor's handle attachment theorem in pushout form
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) presents the sublevel `M_{c+ε} = {f ≤ c + ε}`
of a Morse function as the lower sublevel `M_{c-ε}` with one handle `𝔻 λ × 𝔻 (m - λ)` attached for
each critical point of index `λ` on the level `c`, along closed embeddings
`α : ∂𝔻 λ × 𝔻 (m - λ) → M_{c-ε}` into the level `f⁻¹(c - ε)`. This file reads off what the theorem
says for the simplest Morse functions, one for each extreme case of the index.

* **Index `0`: the quadratic well.** For `f(x) = x²` on `ℝ` at the level `0`, the lower sublevel
  `{x² ≤ -ε}` is empty and the attaching region `∂𝔻 0 × 𝔻 1` of the handle at the minimum `0` is
  empty, so the handle map `𝔻 0 × 𝔻 1 → {x² ≤ ε}` is itself a homeomorphism, carrying the top
  `𝔻 0 × ∂𝔻 1` of the handle onto the two ends `±√ε`
  (`TauCeti.exists_isIso_handle_sq_real`). The sublevel is the interval `[-√ε, √ε]`
  (`TauCeti.setOf_sq_le_eq_Icc`): a handle of index `0` adds a new component, here the only one.
* **Index `1` in dimension `1`: the inverted well.** For `f(x) = -x²` on `ℝ` at the level `0`, the
  critical point `0` has index `1`. The lower sublevel `{-x² ≤ -ε}` is the union of the two rays
  `(-∞, -√ε]` and `[√ε, ∞)` (`TauCeti.setOf_neg_sq_le_neg_eq_union`), and the attaching map
  `∂𝔻 1 × 𝔻 0 → {-x² ≤ -ε}` sends the two points of the attaching sphere to the two ends `-√ε` and
  `√ε` of these rays (`TauCeti.exists_attachingMap_neg_sq_real`). The handle `𝔻 1 × 𝔻 0` is an arc,
  and attaching it joins the two rays into the whole line `{-x² ≤ ε} = ℝ`.
* **Index `n` in dimension `n`: the height on the sphere.** For the height `h = ⟪·, v⟫` on `Sⁿ` at
  its maximum value `1`, the critical point `v` has index `n`. The attaching map
  `∂𝔻 n × 𝔻 0 → {h ≤ 1 - ε}` is a closed embedding whose image is the whole level sphere
  `{h = 1 - ε}` (`TauCeti.exists_attachingMap_sphereHeight`): it lies in that level by the theorem,
  and it covers it because the level `{h = 1 + ε}` above is empty, while the theorem places every
  point of the lower level off the attaching regions on the upper level. Attaching the disc
  `𝔻 n × 𝔻 0` closes up the sphere `{h ≤ 1 + ε} = Sⁿ`.

When the level `c` carries no critical point, the index type of the handles is empty, and the
theorem says that `M_{c+ε}` is homeomorphic to `M_{c-ε}`; this is the deformation across a band
without critical points (`TauCeti.exists_sublevelHomeomorph`), and is recorded below as an example.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Function Set Metric Topology
open scoped Manifold ContDiff

universe u

namespace TauCeti

/-! ### The quadratic well -/

/-- The closed sublevel `{x² ≤ a}` of the quadratic well, for `0 ≤ a`, is the interval
`[-√a, √a]`. -/
theorem setOf_sq_le_eq_Icc {a : ℝ} (ha : 0 ≤ a) : {x : ℝ | x ^ 2 ≤ a} = Icc (-√a) √a := by
  ext x
  simp [Real.sq_le ha]

/-- The critical point `0` of the quadratic well is the only critical point on the level `0`. -/
private theorem criticalPoints_sq_real_inter_preimage_zero :
    criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' {0} = {0} := by
  rw [criticalPoints_sq_real]
  ext x
  simp +contextual

/-- **The handle of the quadratic well.** At the level `0` of `f(x) = x²` on `ℝ`, the handle
attachment theorem (`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle
`𝔻 0 × 𝔻 1`, at the minimum `0`, which has index `0`, to the empty lower sublevel `{x² ≤ -ε}`, along
its empty attaching region. So for some `0 < ε ≤ 1` the handle map `χ : 𝔻 0 × 𝔻 1 → {x² ≤ ε}` is an
isomorphism, and it carries the top `𝔻 0 × ∂𝔻 1` of the handle onto the boundary level `x² = ε`,
the two ends `±√ε` of the interval `{x² ≤ ε} = [-√ε, √ε]`. -/
theorem exists_isIso_handle_sq_real :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ χ : TopCat.of (TopCat.disk.{0} 0 × TopCat.disk.{0} 1) ⟶ TopCat.of {x : ℝ | x ^ 2 ≤ ε},
        IsIso χ ∧ ∀ w, (χ w : ℝ) ^ 2 = ε ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion 1) := by
  have hcompact : IsCompact ((fun x : ℝ ↦ x ^ 2) ⁻¹' Icc (0 - 1) (0 + 1)) :=
    (isProperMap_pow two_ne_zero).isCompact_preimage isCompact_Icc
  obtain ⟨ε, hε, hε1, α, χ, j, hpush, -, -, -, htop, -⟩ :=
    isMorse_sq_real.exists_isPushout_sublevel_handles one_pos hcompact
  -- The lower sublevel is empty, so the attaching map is an isomorphism of empty spaces, and so is
  -- its pushout, the coproduct of the handle maps.
  have hempty : IsEmpty {x : ℝ | x ^ 2 ≤ 0 - ε} :=
    ⟨fun x ↦ by have h : (x : ℝ) ^ 2 ≤ 0 - ε := x.2; nlinarith [sq_nonneg (x : ℝ)]⟩
  have hα : IsIso (Sigma.desc α) := by
    -- A map into an empty space is a map between empty spaces, hence a homeomorphism.
    have hiso {X Y : TopCat.{0}} (g : X ⟶ Y) (hY : IsEmpty (ToType Y)) : IsIso g := by
      have hX : IsEmpty (ToType X) := ⟨fun x ↦ hY.false (g x)⟩
      exact (TopCat.isIso_iff_isHomeomorph g).2 ⟨g.hom.continuous,
        fun s _ ↦ by rw [s.eq_empty_of_isEmpty, image_empty]; exact isOpen_empty,
        fun x ↦ hX.elim x, fun y ↦ hY.elim y⟩
    exact hiso _ hempty
  have hχ : IsIso (Sigma.desc χ) := hpush.isIso_inr_of_isIso
  -- The only critical point on the level is `0`, so the coproduct has a single summand.
  let p₀ : ↥(criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' {0}) :=
    ⟨0, criticalPoints_sq_real_inter_preimage_zero.symm ▸ rfl⟩
  let _ : Unique ↥(criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' {0}) :=
    { default := p₀
      uniq := fun p ↦ Subtype.ext (by
        simpa [criticalPoints_sq_real_inter_preimage_zero] using p.2) }
  have hχ₀ : IsIso (χ p₀) := by
    rw [← Sigma.ι_comp_desc χ p₀, show p₀ = default from rfl, ← coproductUniqueIso_inv]
    infer_instance
  -- Read the handle of index `0` and coindex `1` as `𝔻 0 × 𝔻 1`.
  have hk : manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) (p₀ : ℝ) = 0 := by
    simpa using morseIndex_norm_sq (0 : ℝ)
  have key : ∀ (k l : ℕ) (b : ℝ), k = 0 → l = 1 → b = ε →
      ∀ χ' : TopCat.of (TopCat.disk.{0} k × TopCat.disk.{0} l) ⟶ TopCat.of {x : ℝ | x ^ 2 ≤ b},
        IsIso χ' → (∀ w, (χ' w : ℝ) ^ 2 = b ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion l)) →
          ∃ χ : TopCat.of (TopCat.disk.{0} 0 × TopCat.disk.{0} 1) ⟶
            TopCat.of {x : ℝ | x ^ 2 ≤ ε},
            IsIso χ ∧ ∀ w, (χ w : ℝ) ^ 2 = ε ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion 1) := by
    rintro k l b rfl rfl rfl χ' hχ' htop'
    exact ⟨χ', hχ', htop'⟩
  refine ⟨ε, hε, hε1, key _ _ _ (by rw [hk]) (by rw [hk, Module.finrank_self]) (zero_add ε)
    (χ p₀) hχ₀ fun w ↦ ?_⟩
  simpa using htop p₀ w

/-! ### The inverted well -/

/-- The closed sublevel `{-x² ≤ -a}` of the inverted well is the union of the two rays
`(-∞, -√a]` and `[√a, ∞)`; for `a ≤ 0` they cover the line, since then `√a = 0`. -/
theorem setOf_neg_sq_le_neg_eq_union (a : ℝ) :
    {x : ℝ | -x ^ 2 ≤ -a} = Iic (-√a) ∪ Ici √a := by
  ext x
  simp only [mem_ofPred_eq, neg_le_neg_iff, mem_union, mem_Iic, mem_Ici]
  rw [← Real.sqrt_le_sqrt_iff (sq_nonneg x), Real.sqrt_sq_eq_abs, le_abs']

/-- The inverted well `x ↦ -x²` is a Morse function on `ℝ`. -/
theorem isMorse_neg_sq_real : IsMorse 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) :=
  isMorse_sq_real.neg

/-- The only critical point of the inverted well is `0`. -/
theorem criticalPoints_neg_sq_real : criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) = {0} :=
  (criticalPoints_neg (f := fun x : ℝ ↦ x ^ 2)).trans criticalPoints_sq_real

/-- The critical point `0` of the inverted well has Morse index `1`. -/
theorem manifoldMorseIndex_neg_sq_real :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) 0 = 1 := by
  have hcrit : (0 : ℝ) ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) := by
    simp [criticalPoints_sq_real]
  have hnd := isMorse_sq_real.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hcrit)
  have h := hnd.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have h0 : manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0 = 0 := by
    simpa using morseIndex_norm_sq (0 : ℝ)
  rw [h0, Module.finrank_self] at h
  exact h

/-- A map from the two points of `∂𝔻 1 × 𝔻 0` to `ℝ` which is injective and takes values of square
`a` has image `{-√a, √a}`. -/
private theorem range_eq_of_injective_of_sq_eq {a : ℝ}
    (g : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 → ℝ) (hg : Function.Injective g)
    (hsq : ∀ s, g s ^ 2 = a) : range g = {-√a, √a} := by
  have hmem (s) : g s = -√a ∨ g s = √a := by
    have h := Real.sqrt_sq_eq_abs (g s)
    rw [hsq s] at h
    rcases abs_eq (Real.sqrt_nonneg a) |>.1 h.symm with h' | h'
    exacts [Or.inr h', Or.inl h']
  -- The two points `(±1, 0)` of `∂𝔻 1 × 𝔻 0` go to the two square roots, in some order.
  let sp : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 :=
    (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, diskCenter 0)
  let sm : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 :=
    (ULift.up ⟨EuclideanSpace.single 0 (-1), by simp⟩, diskCenter 0)
  have hne : g sp ≠ g sm := hg.ne fun h ↦ by
    have := congrArg (fun s : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 ↦
      (s.1.down : EuclideanSpace ℝ (Fin 1)) 0) h
    norm_num [sp, sm] at this
  refine Subset.antisymm (range_subset_iff.2 fun s ↦ ?_) fun y hy ↦ ?_
  · rcases hmem s with h | h <;> simp [h]
  · rcases hy with rfl | rfl <;> rcases hmem sp with hp | hp <;> rcases hmem sm with hm | hm
    all_goals first
      | exact ⟨sp, hp⟩ | exact ⟨sm, hm⟩ | exact absurd (hp.trans hm.symm) hne

/-- **The attaching map of the inverted well.** At the level `0` of `f(x) = -x²` on `ℝ`, the handle
attachment theorem (`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle
`𝔻 1 × 𝔻 0`, at the maximum `0`, which has index `1`. So for some `0 < ε ≤ 1` its attaching map
`α : ∂𝔻 1 × 𝔻 0 → {-x² ≤ -ε}` is a closed embedding sending the two points of the attaching sphere
`∂𝔻 1` onto the two points `-√ε` and `√ε` of the level `-x² = -ε`. These are the ends of the two
rays `(-∞, -√ε]` and `[√ε, ∞)` that make up the lower sublevel
(`TauCeti.setOf_neg_sq_le_neg_eq_union`), so in the pushout of the theorem the arc `𝔻 1 × 𝔻 0`
joins the two rays into the line `{-x² ≤ ε} = ℝ`. -/
theorem exists_attachingMap_neg_sq_real :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ α : TopCat.of (TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0) ⟶
          TopCat.of {x : ℝ | -x ^ 2 ≤ -ε},
        IsClosedEmbedding α ∧ range (fun s ↦ (α s : ℝ)) = {-√ε, √ε} := by
  have hcompact : IsCompact ((fun x : ℝ ↦ -x ^ 2) ⁻¹' Icc (0 - 1) (0 + 1)) :=
    ((Homeomorph.neg ℝ).isProperMap.comp (isProperMap_pow two_ne_zero)).isCompact_preimage
      isCompact_Icc
  obtain ⟨ε, hε, hε1, α, -, -, -, hemb, -, hlev, -, -⟩ :=
    isMorse_neg_sq_real.exists_isPushout_sublevel_handles one_pos hcompact
  have hlevel : criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) ∩ (fun x : ℝ ↦ -x ^ 2) ⁻¹' {0} =
      {0} := by
    rw [criticalPoints_neg_sq_real]
    ext x
    simp +contextual
  let p₀ : ↥(criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) ∩ (fun x : ℝ ↦ -x ^ 2) ⁻¹' {0}) :=
    ⟨0, hlevel.symm ▸ rfl⟩
  -- Read the attaching region of index `1` and coindex `0` as `∂𝔻 1 × 𝔻 0`.
  have hk : manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) (p₀ : ℝ) = 1 :=
    manifoldMorseIndex_neg_sq_real
  have key : ∀ (k l : ℕ) (b : ℝ), k = 1 → l = 0 → b = -ε →
      ∀ α' : TopCat.of (TopCat.diskBoundary.{0} k × TopCat.disk.{0} l) ⟶
          TopCat.of {x : ℝ | -x ^ 2 ≤ b},
        IsClosedEmbedding α' → (∀ s, -(α' s : ℝ) ^ 2 = b) →
          ∃ α : TopCat.of (TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0) ⟶
              TopCat.of {x : ℝ | -x ^ 2 ≤ -ε},
            IsClosedEmbedding α ∧ range (fun s ↦ (α s : ℝ)) = {-√ε, √ε} := by
    rintro k l b rfl rfl rfl α' hα' hlev'
    refine ⟨α', hα', range_eq_of_injective_of_sq_eq _
      (Subtype.val_injective.comp hα'.injective) fun s ↦ ?_⟩
    simpa using hlev' s
  exact ⟨ε, hε, hε1, key _ _ _ hk (by rw [hk, Module.finrank_self]) (zero_sub ε) (α p₀) (hemb p₀)
    (hlev p₀)⟩

/-! ### The height on the sphere -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- **The attaching map at the top of the sphere.** At the level `1` of the height `h = ⟪·, v⟫` on
the unit sphere `Sⁿ`, the handle attachment theorem
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle `𝔻 n × 𝔻 0`, at the north
pole `v`, which has index `n`. So for some `0 < ε ≤ 1` its attaching map
`α : ∂𝔻 n × 𝔻 0 → {h ≤ 1 - ε}` is a closed embedding whose image is the whole level sphere
`{h = 1 - ε}`. The theorem puts the image in that level; it fills the level because the level
`{h = 1 + ε}` above the maximum is empty, while the theorem sends every point of `{h = 1 - ε}` off
the attaching region to that upper level. So in the pushout of the theorem the disc `𝔻 n × 𝔻 0` is
attached along the whole level sphere, closing up `{h ≤ 1 + ε} = Sⁿ`. -/
theorem exists_attachingMap_sphereHeight (v : sphere (0 : E) 1) :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ α : TopCat.of (TopCat.diskBoundary.{u} n × TopCat.disk.{u} 0) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 - ε},
        IsClosedEmbedding α ∧
          range (fun s ↦ (α s : sphere (0 : E) 1)) = {x | sphereHeight v x = 1 - ε} := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨ε, hε, hε1, α, -, j, -, hemb, -, hlev, -, hj⟩ :=
    (isMorse_sphereHeight (n := n) v).exists_isPushout_sublevel_handles (c := 1) one_pos
      (isClosed_Icc.preimage (contMDiff_sphereHeight (n := n) (m := 0) v).continuous).isCompact
  have hlevel : criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1} = {v} := by
    ext x
    simp only [criticalPoints_sphereHeight, mem_inter_iff, mem_insert_iff, mem_singleton_iff,
      mem_preimage]
    constructor
    · rintro ⟨hx | hx, h⟩
      · exact hx
      · rw [hx, sphereHeight_neg_self] at h
        norm_num at h
    · rintro rfl
      exact ⟨Or.inl rfl, sphereHeight_self x⟩
  let p₀ : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1}) :=
    ⟨v, hlevel.symm ▸ rfl⟩
  have huniq (p : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1})) : p = p₀ :=
    Subtype.ext (by simpa only [hlevel, mem_singleton_iff] using p.2)
  -- Every point of the level `h = 1 - ε` lies on the attaching region: otherwise the theorem would
  -- send it to the empty level `h = 1 + ε`.
  have hcover (x : {x | sphereHeight v x ≤ 1 - ε}) (hx : sphereHeight v x = 1 - ε) :
      x ∈ range (α p₀) := by
    by_contra hx'
    have h := (hj x fun p ↦ huniq p ▸ hx').2 hx
    linarith [sphereHeight_le_one v (j x : sphere (0 : E) 1)]
  -- Read the attaching region of index `n` and coindex `0` as `∂𝔻 n × 𝔻 0`.
  have hk : manifoldMorseIndex (𝓡 n) (sphereHeight v) (p₀ : sphere (0 : E) 1) = n :=
    manifoldMorseIndex_sphereHeight_self v
  have key : ∀ (k l : ℕ), k = n → l = 0 →
      ∀ α' : TopCat.of (TopCat.diskBoundary.{u} k × TopCat.disk.{u} l) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 - ε},
        IsClosedEmbedding α' → (∀ s, sphereHeight v (α' s) = 1 - ε) →
          (∀ x : {x | sphereHeight v x ≤ 1 - ε}, sphereHeight v x = 1 - ε → x ∈ range α') →
          ∃ α : TopCat.of (TopCat.diskBoundary.{u} n × TopCat.disk.{u} 0) ⟶
              TopCat.of {x | sphereHeight v x ≤ 1 - ε},
            IsClosedEmbedding α ∧
              range (fun s ↦ (α s : sphere (0 : E) 1)) = {x | sphereHeight v x = 1 - ε} := by
    rintro k l rfl rfl α' hα' hlev' hcover'
    refine ⟨α', hα', Subset.antisymm (range_subset_iff.2 hlev') fun x hx ↦ ?_⟩
    obtain ⟨s, hs⟩ := hcover' ⟨x, le_of_eq hx⟩ hx
    exact ⟨s, congrArg Subtype.val hs⟩
  exact ⟨ε, hε, hε1, key _ _ hk (by rw [hk, finrank_euclideanSpace_fin, Nat.sub_self]) (α p₀)
    (hemb p₀) (hlev p₀) hcover⟩

end Sphere

/-! ### A level without critical points -/

/-- With no critical point on the level `c`, the handle attachment theorem attaches no handle, and
says that `{f ≤ c + ε}` is homeomorphic to `{f ≤ c - ε}`, as the deformation across a band without
critical points does (`TauCeti.exists_sublevelHomeomorph`). -/
example {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type u}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}
    (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hc : criticalPoints I f ∩ f ⁻¹' {c} = ∅) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ Nonempty ({x | f x ≤ c - ε} ≃ₜ {x | f x ≤ c + ε}) := by
  obtain ⟨ε, hε, hεδ, α, χ, j, hpush, -⟩ := hf.exists_isPushout_sublevel_handles hδ hcompact
  have : IsEmpty ↥(criticalPoints I f ∩ f ⁻¹' {c}) := by rw [hc]; infer_instance
  -- The map between the coproducts over the empty set of handles is an isomorphism, since it is
  -- one on each of the no summands (`isEmptyElim`), and so is its pushout `j`.
  have : IsIso j := hpush.isIso_inl_of_isIso (@Limits.Sigma.map_isIso _ _ _ _ _ _ _ isEmptyElim)
  exact ⟨ε, hε, hεδ, ⟨TopCat.homeoOfIso (asIso j)⟩⟩

end TauCeti
