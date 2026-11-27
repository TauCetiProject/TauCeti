/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Projective

/-!
# The negative index of a bilinear form

The negative index is the supremum, in `ℕ∞`, of the dimensions of finite-dimensional subspaces
on which the diagonal of a bilinear form over a linearly ordered field is strictly negative
away from zero. This definition also applies to infinite-dimensional spaces. Restricting the
admissible vectors to a submodule gives `LinearMap.BilinForm.negativeIndexOn`. In finite dimension
the index agrees with the negative index of inertia of the associated quadratic form.

The index is monotone in the admissible submodule and commutes with directed unions. These
facts give the algebraic part of defining the Morse index by compactly supported variations and
computing it along an exhaustion.

The index is unchanged by positive scaling of the form and by linear isomorphisms, and pulling
the form back along an injective linear map computes the index on the image; so it is monotone
under inclusion of test spaces. If `C` is orthogonal to `A` on both sides and the form is
nonnegative on `C`, the index on `A ⊔ C` is the index on `A`
(`LinearMap.BilinForm.negativeIndexOn_sup_eq_left`). This is the algebraic step of the finite
reduction in the proof of the Morse index theorem: the index form on fields along a geodesic
vanishing at its ends splits into broken Jacobi fields, a finite-dimensional space, and fields
vanishing at the break points, on which the form is positive. The companion statement for
nullity is `LinearMap.BilinForm.finrank_ker_restrict_sup`.

## Main definitions and results

* `LinearMap.BilinForm.negativeIndexOn` and `LinearMap.BilinForm.negativeIndex`: the negative
  index on an admissible submodule and on the whole space.
* `LinearMap.BilinForm.negativeIndex_eq_sigNeg` and
  `LinearMap.BilinForm.negativeIndexOn_eq_sigNeg_restrict`: in finite dimension the index is the
  negative index of inertia.
* `LinearMap.BilinForm.negativeIndexOn_comp_of_injective`,
  `LinearMap.BilinForm.negativeIndex_congr`, `LinearMap.BilinForm.negativeIndex_restrict` and
  `LinearMap.BilinForm.negativeIndexOn_smul_of_pos`: transport along injective linear maps and
  isomorphisms, restriction and positive scaling.
* `LinearMap.BilinForm.negativeIndexOn_sup_eq_left`: the index on an orthogonal sum with a
  nonnegative summand.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §15.
-/

public noncomputable section

open Module

namespace LinearMap.BilinForm

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- The negative index of a bilinear form on an admissible submodule, allowing infinity. -/
def negativeIndexOn (B : LinearMap.BilinForm 𝕜 V) (S : Submodule 𝕜 V) : ℕ∞ :=
  ⨆ (W : Submodule 𝕜 V) (_ : Module.Finite 𝕜 W) (_ : W ≤ S)
    (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank 𝕜 W : ℕ∞)

/-- The negative index of a bilinear form over a linearly ordered field, allowing infinity. -/
def negativeIndex (B : LinearMap.BilinForm 𝕜 V) : ℕ∞ :=
  B.negativeIndexOn ⊤

variable (B : LinearMap.BilinForm 𝕜 V) {S T : Submodule 𝕜 V}

/-- The negative index is the supremum of the dimensions of its finite negative subspaces. -/
theorem negativeIndexOn_def :
    B.negativeIndexOn S =
      ⨆ (W : Submodule 𝕜 V) (_ : Module.Finite 𝕜 W) (_ : W ≤ S)
        (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank 𝕜 W : ℕ∞) :=
  (rfl)

/-- The negative index allows every vector as an admissible variation. -/
theorem negativeIndex_def : B.negativeIndex = B.negativeIndexOn ⊤ :=
  (rfl)

/-- An upper bound for the index is exactly an upper bound for every finite negative subspace. -/
theorem negativeIndexOn_le_iff {n : ℕ∞} :
    B.negativeIndexOn S ≤ n ↔
      ∀ (W : Submodule 𝕜 V) [Module.Finite 𝕜 W], W ≤ S →
        (∀ w ∈ W, w ≠ 0 → B w w < 0) → (finrank 𝕜 W : ℕ∞) ≤ n := by
  simp only [negativeIndexOn, iSup_le_iff]

/-- Every finite-dimensional negative subspace supplies a lower bound for the index. -/
theorem finrank_le_negativeIndexOn (W : Submodule 𝕜 V) [Module.Finite 𝕜 W]
    (hWS : W ≤ S) (hW : ∀ w ∈ W, w ≠ 0 → B w w < 0) :
    (finrank 𝕜 W : ℕ∞) ≤ B.negativeIndexOn S :=
  le_iSup_of_le W <| le_iSup_of_le ‹Module.Finite 𝕜 W› <|
    le_iSup_of_le hWS <| le_iSup_of_le hW le_rfl

/-- A finite lower bound for the index is realized by a negative subspace of that dimension. -/
theorem le_negativeIndexOn_iff {n : ℕ} :
    (n : ℕ∞) ≤ B.negativeIndexOn S ↔
      ∃ W : Submodule 𝕜 V, Module.Finite 𝕜 W ∧ W ≤ S ∧
        (∀ w ∈ W, w ≠ 0 → B w w < 0) ∧ finrank 𝕜 W = n := by
  constructor
  · intro h
    cases n with
    | zero =>
      exact ⟨⊥, inferInstance, bot_le, by simp, by simp⟩
    | succ n =>
      have hlt : (n : ℕ∞) < B.negativeIndexOn S := by
        simpa only [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff] using h
      simp only [negativeIndexOn_def, lt_iSup_iff] at hlt
      obtain ⟨W, hfin, hWS, hneg, hdim⟩ := hlt
      let := hfin
      obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
        (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hdim))
      have hmap := hv.map' W.subtype (LinearMap.ker_eq_bot.mpr W.subtype_injective)
      let U := Submodule.span 𝕜 (Set.range (W.subtype ∘ v))
      have hUW : U ≤ W := Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact (v i).property)
      exact ⟨U, Module.Finite.span_of_finite 𝕜 (Set.finite_range _), hUW.trans hWS,
        fun w hw ↦ hneg w (hUW hw),
        by simpa [U] using finrank_span_eq_card hmap⟩
  · rintro ⟨W, hfin, hWS, hneg, rfl⟩
    exact B.finrank_le_negativeIndexOn W hWS hneg

/-- The negative index is infinite precisely when negative subspaces have every finite dimension. -/
theorem negativeIndexOn_eq_top_iff :
    B.negativeIndexOn S = ⊤ ↔
      ∀ n : ℕ, ∃ W : Submodule 𝕜 V, Module.Finite 𝕜 W ∧ W ≤ S ∧
        (∀ w ∈ W, w ≠ 0 → B w w < 0) ∧ finrank 𝕜 W = n := by
  simp only [ENat.eq_top_iff_forall_ge, le_negativeIndexOn_iff]

/-- Enlarging the admissible submodule cannot decrease the negative index. -/
theorem negativeIndexOn_mono (hST : S ≤ T) :
    B.negativeIndexOn S ≤ B.negativeIndexOn T := by
  rw [negativeIndexOn_le_iff]
  intro W _ hWS hW
  exact B.finrank_le_negativeIndexOn W (hWS.trans hST) hW

/-- On a finite-dimensional admissible submodule the negative index is at most its dimension. -/
theorem negativeIndexOn_le_finrank [Module.Finite 𝕜 S] :
    B.negativeIndexOn S ≤ finrank 𝕜 S := by
  rw [negativeIndexOn_le_iff]
  intro W _ hWS _
  exact ENat.natCast_le_natCast.mpr (Submodule.finrank_mono hWS)

/-! ### Transport along injective linear maps -/

section Comp

variable {V' : Type*} [AddCommGroup V'] [Module 𝕜 V']

/-- Pulling a form back along an injective linear map computes the negative index on the image
of the admissible submodule. -/
theorem negativeIndexOn_comp_of_injective {f : V' →ₗ[𝕜] V} (hf : Function.Injective f)
    (S : Submodule 𝕜 V') :
    (B.comp f f).negativeIndexOn S = B.negativeIndexOn (S.map f) := by
  apply le_antisymm
  · rw [negativeIndexOn_le_iff]
    intro W _ hWS hW
    rw [(Submodule.equivMapOfInjective f hf W).finrank_eq]
    refine B.finrank_le_negativeIndexOn _ (Submodule.map_mono hWS) ?_
    rintro _ ⟨w, hw, rfl⟩ hw0
    simpa using hW w hw (by rintro rfl; simp at hw0)
  · rw [negativeIndexOn_le_iff]
    intro W _ hWS hW
    have hWf : W ≤ LinearMap.range f :=
      hWS.trans (LinearMap.range_eq_map f ▸ Submodule.map_mono le_top)
    let e := (Submodule.equivMapOfInjective f hf (W.comap f)).trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_of_le hWf))
    have : Module.Finite 𝕜 (W.comap f) := Module.Finite.equiv e.symm
    rw [← LinearEquiv.finrank_eq e]
    refine (B.comp f f).finrank_le_negativeIndexOn _ (fun w hw ↦ ?_) fun w hw hw0 ↦ ?_
    · obtain ⟨s, hs, hsw⟩ := hWS hw
      exact hf hsw ▸ hs
    · simpa using hW (f w) hw (by simpa [map_eq_zero_iff f hf] using hw0)

/-- The negative index of a pullback along an injective linear map is the negative index on its
range. -/
theorem negativeIndex_comp_of_injective {f : V' →ₗ[𝕜] V} (hf : Function.Injective f) :
    (B.comp f f).negativeIndex = B.negativeIndexOn (LinearMap.range f) := by
  rw [negativeIndex, negativeIndexOn_comp_of_injective B hf, LinearMap.range_eq_map]

/-- Restricting the admissible vectors along an injective linear map cannot increase the negative
index. -/
theorem negativeIndex_comp_le_of_injective {f : V' →ₗ[𝕜] V} (hf : Function.Injective f) :
    (B.comp f f).negativeIndex ≤ B.negativeIndex := by
  rw [negativeIndex_comp_of_injective B hf]
  exact B.negativeIndexOn_mono le_top

/-- The negative index is invariant under linear isomorphisms. -/
@[simp]
theorem negativeIndex_congr (e : V ≃ₗ[𝕜] V') :
    (LinearMap.BilinForm.congr e B).negativeIndex = B.negativeIndex := by
  have h : LinearMap.BilinForm.congr e B = B.comp e.symm e.symm := by
    ext
    simp [LinearMap.BilinForm.congr_apply]
  rw [h, negativeIndex_comp_of_injective B e.symm.injective, LinearEquiv.range, negativeIndex]

end Comp

/-- The negative index of the restriction of a form to a submodule is its negative index on that
submodule. -/
@[simp]
theorem negativeIndex_restrict : (B.restrict S).negativeIndex = B.negativeIndexOn S := by
  have h : B.restrict S = B.comp S.subtype S.subtype := by
    ext
    simp
  rw [h, negativeIndex_comp_of_injective B S.injective_subtype, Submodule.range_subtype]

variable [IsStrictOrderedRing 𝕜]

/-- Scaling a form by a positive constant does not change its negative index. -/
@[simp]
theorem negativeIndexOn_smul_of_pos {a : 𝕜} (ha : 0 < a) :
    (a • B).negativeIndexOn S = B.negativeIndexOn S := by
  have key (w : V) : (a • B) w w < 0 ↔ B w w < 0 := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact ⟨fun h ↦ neg_of_mul_neg_right h ha.le, mul_neg_of_pos_of_neg ha⟩
  simp only [negativeIndexOn_def, key]

/-- Scaling a form by a positive constant does not change its negative index. -/
@[simp]
theorem negativeIndex_smul_of_pos {a : 𝕜} (ha : 0 < a) :
    (a • B).negativeIndex = B.negativeIndex :=
  negativeIndexOn_smul_of_pos B ha

/-- The negative index vanishes precisely when the diagonal is nonnegative. -/
theorem negativeIndexOn_eq_zero_iff :
    B.negativeIndexOn S = 0 ↔ ∀ v ∈ S, 0 ≤ B v v := by
  constructor
  · intro h v hv
    by_contra hn
    have hneg : B v v < 0 := lt_of_not_ge hn
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hneg
    have hspan : ∀ w ∈ (𝕜 ∙ v), w ≠ 0 → B w w < 0 := by
      intro w hw hw0
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hw0
      rw [smul_left, smul_right, ← mul_assoc]
      exact mul_neg_of_pos_of_neg (mul_self_pos.mpr ha) hneg
    have hle := B.finrank_le_negativeIndexOn (𝕜 ∙ v)
      ((Submodule.span_singleton_le_iff_mem v S).mpr hv) hspan
    rw [finrank_span_singleton hv0, h] at hle
    simp at hle
  · intro h
    apply le_antisymm _ bot_le
    rw [negativeIndexOn_le_iff]
    intro W _ hWS hW
    have hbot : W = ⊥ := by
      apply (Submodule.eq_bot_iff W).mpr
      intro w hw
      by_contra hw0
      exact (not_lt_of_ge (h w (hWS hw))) (hW w hw hw0)
    simp [hbot]

/-- The negative index vanishes precisely when the form is nonnegative on every vector. -/
theorem negativeIndex_eq_zero_iff :
    B.negativeIndex = 0 ↔ ∀ v, 0 ≤ B v v := by
  simp [negativeIndex, negativeIndexOn_eq_zero_iff]

/-- The negative index commutes with directed unions of admissible submodules. -/
theorem negativeIndexOn_iSup_of_directed {ι : Sort*} (S : ι → Submodule 𝕜 V)
    (hS : Directed (· ≤ ·) S) :
    B.negativeIndexOn (⨆ i, S i) = ⨆ i, B.negativeIndexOn (S i) := by
  cases isEmpty_or_nonempty ι
  · simp [negativeIndexOn_eq_zero_iff]
  apply le_antisymm
  · rw [negativeIndexOn_le_iff]
    intro W _ hW hneg
    have hcompact := (Submodule.fg_iff_compact W).mp
      (Module.Finite.iff_fg.mp ‹Module.Finite 𝕜 W›)
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hcompact _ _ (Set.range_nonempty S) hS.directedOn_range
      isLUB_iSup hW
    exact le_iSup_of_le n (B.finrank_le_negativeIndexOn W hn hneg)
  · exact iSup_le fun n ↦ B.negativeIndexOn_mono (le_iSup S n)

/-- Negativity on a submodule is positive definiteness of the restricted negative quadratic form. -/
theorem posDef_restrict_neg_toQuadraticMap_iff (W : Submodule 𝕜 V) :
    ((-B.toQuadraticMap).restrict W).PosDef ↔ ∀ w ∈ W, w ≠ 0 → B w w < 0 := by
  simp only [QuadraticMap.PosDef, QuadraticMap.restrict_apply, _root_.neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos, Subtype.forall,
    ne_eq, Submodule.mk_eq_zero]

/-- In finite dimension the extended negative index is the usual negative index of inertia. -/
theorem negativeIndex_eq_sigNeg [Module.Finite 𝕜 V] :
    B.negativeIndex = (sigNeg B.toQuadraticMap : ℕ∞) := by
  apply le_antisymm
  · rw [negativeIndex, negativeIndexOn_le_iff]
    intro W _ _ hW
    exact ENat.natCast_le_natCast.mpr
      (le_sigNeg_of_negDef B.toQuadraticMap ((B.posDef_restrict_neg_toQuadraticMap_iff W).mpr hW))
  · obtain ⟨W, hW, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef B.toQuadraticMap
    rw [← hW]
    exact B.finrank_le_negativeIndexOn W le_top
      ((B.posDef_restrict_neg_toQuadraticMap_iff W).mp hneg)

/-- On a finite-dimensional admissible submodule the negative index is the negative index of
inertia of the restricted form; in particular it is finite. -/
theorem negativeIndexOn_eq_sigNeg_restrict [Module.Finite 𝕜 S] :
    B.negativeIndexOn S = (sigNeg (B.restrict S).toQuadraticMap : ℕ∞) := by
  rw [← negativeIndex_restrict, negativeIndex_eq_sigNeg]

/-! ### Orthogonal splittings with a nonnegative summand -/

section Splitting

variable {A C : Submodule 𝕜 V}

/-- **Index reduction.** If `C` is orthogonal to `A` on both sides and the form is nonnegative on
`C`, then the negative index on `A ⊔ C` is the negative index on `A`. -/
theorem negativeIndexOn_sup_eq_left (hAC : ∀ a ∈ A, ∀ c ∈ C, B a c = 0)
    (hCA : ∀ c ∈ C, ∀ a ∈ A, B c a = 0) (hC : ∀ c ∈ C, 0 ≤ B c c) :
    B.negativeIndexOn (A ⊔ C) = B.negativeIndexOn A := by
  refine le_antisymm ?_ (B.negativeIndexOn_mono le_sup_left)
  rw [negativeIndexOn_le_iff]
  intro W _ hW hneg
  -- Split every vector of `W` linearly as `a + c`, lifting `W` through `A × C → A ⊔ C`.
  let p : (A × C) →ₗ[𝕜] V := A.subtype.coprod C.subtype
  have hp : LinearMap.range p = A ⊔ C := by
    simp [p, LinearMap.range_coprod]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property p.rangeRestrict
    (Submodule.inclusion (hW.trans hp.ge)) p.surjective_rangeRestrict
  have hsplit (w : W) : ((h w).fst : V) + (h w).snd = w := by
    simpa [p] using congr(($hh w : V))
  let φ : W →ₗ[𝕜] V := A.subtype ∘ₗ LinearMap.fst 𝕜 A C ∘ₗ h
  have hφ (w : W) : φ w = (h w).fst := rfl
  -- The `A`-component of `w` is at least as negative as `w`.
  have hle (w : W) : B (φ w) (φ w) ≤ B w w := by
    rw [← hsplit w, hφ]
    simp only [map_add, LinearMap.add_apply, hAC _ (h w).fst.property _ (h w).snd.property,
      hCA _ (h w).snd.property _ (h w).fst.property, add_zero, zero_add]
    exact le_add_of_nonneg_right (hC _ (h w).snd.property)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hwC : (w : V) ∈ C := by
      rw [← hsplit w, ← hφ, LinearMap.mem_ker.mp hw, zero_add]
      exact (h w).snd.property
    exact (hneg w w.property (by simpa using hw0)).not_ge (hC w hwC)
  rw [← LinearMap.finrank_range_of_inj hinj]
  refine B.finrank_le_negativeIndexOn _ ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact (h w).fst.property
  · rintro _ ⟨w, rfl⟩ hw0
    have hw : (w : V) ≠ 0 := fun h0 ↦ hw0 (by rw [show w = 0 from Subtype.ext h0, map_zero])
    exact (hle w).trans_lt (hneg w w.property hw)

end Splitting

end LinearMap.BilinForm
