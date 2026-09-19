/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-!
# Smooth concordance of smooth embeddings

Two smooth embeddings `f g : M → N` are **concordant** when they are the two ends of a smooth
embedding `M × [0, 1] → N × [0, 1]` which sends `M × {0}`, `M × {1}` and `M × (0, 1)` into
`N × {0}`, `N × {1}` and `N × (0, 1)` respectively. For knots, `M` is the circle and the track
is an annulus in `N × [0, 1]`; this is the relation underlying the knot concordance group.

To avoid manifolds with boundary, a concordance is stored in its *collared* form: a `C^n` embedding
`F : M × ℝ → N × ℝ` which is the product `f × id` on some neighborhood of the initial end, the
product `g × id` on some neighborhood of the final end, and maps `M × (0, 1)` into
`N × (0, 1)`. Its restriction to `M × [0, 1]` is therefore a concordance in the sense above which
is a product near both ends; by the collar theorem, every smooth concordance can be made a product
near its ends, so no concordances are lost. The product ends are what make concordances stack
smoothly.

The relation is defined here for arbitrary smooth embeddings, in line with defining isotopy once
for general maps; smooth knot concordance is the case of `TauCeti.SmoothCircleEmbedding`, whose
source is the circle.

## Main definitions

* `TauCeti.SmoothEmbedding.Concordance f g`: a `C^n` concordance from `f` to `g`, in collared
  form.
* `TauCeti.SmoothEmbedding.Concordance.refl`, `symm`, `trans`: the constant concordance, the
  reversed concordance, and the stacked concordance.
* `TauCeti.SmoothEmbedding.Concordance.ofDiffeotopy`: the trace of a diffeotopy, a concordance
  from an embedding to its image under the final diffeomorphism.
* `TauCeti.SmoothEmbedding.Concordant`: the concordance relation.

## Main results

* `TauCeti.SmoothEmbedding.Concordant.equivalence`: for a finite-dimensional ambient model,
  concordance is an equivalence relation.
* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.concordant`: smoothly ambient isotopic
  embeddings are concordant.

## Implementation notes

Stacking two concordances glues two immersions along an open cover. Mathlib's
`Manifold.IsImmersion` requires a single complement for all points, so the glued map is shown to
be an immersion with `TauCeti.isImmersion_iff_forall_isImmersionAt`, which needs the model of `N`
to be finite-dimensional. Only `trans` and the statements depending on it carry that assumption.

The trace of a diffeotopy is reparametrized by `Real.smoothTransition`, which is `C^∞` but not
analytic; `ofDiffeotopy` therefore assumes `n ≤ ∞`.

## References

* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448, for
  concordance of embeddings.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for knot concordance.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Manifold Topology
open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

/-- A `C^n` **concordance** from the smooth embedding `f` to the smooth embedding `g`, in collared
form: a `C^n` embedding of `M × ℝ` into `N × ℝ` which is `f × id` and `g × id` on neighborhoods
of the initial and final ends, and maps `M × (0, 1)` into `N × (0, 1)`. -/
structure Concordance (f g : SmoothEmbedding I J n M N) where
  /-- The track of the concordance, a smooth embedding of `M × ℝ` into `N × ℝ`. -/
  toSmoothEmbedding : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ)
  /-- The track is the product of `f` with the identity on a neighborhood of the initial end. -/
  exists_pos_apply_eq_left' :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), t ≤ ε → toSmoothEmbedding (x, t) = (f x, t)
  /-- The track is the product of `g` with the identity on a neighborhood of the final end. -/
  exists_pos_apply_eq_right' :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), 1 - ε ≤ t → toSmoothEmbedding (x, t) = (g x, t)
  /-- The track maps the open slab `M × (0, 1)` into the open slab `N × (0, 1)`. -/
  snd_apply_mem_Ioo' (x : M) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (toSmoothEmbedding (x, t)).2 ∈ Ioo 0 1

/-- Two smooth embeddings are **concordant** when there is a concordance from one to the other. -/
def Concordant (f g : SmoothEmbedding I J n M N) : Prop :=
  Nonempty (Concordance f g)

namespace Concordance

variable {f g h : SmoothEmbedding I J n M N}

instance instFunLike : FunLike (Concordance f g) (M × ℝ) (N × ℝ) where
  coe F := F.toSmoothEmbedding
  coe_injective F G hFG := by
    cases F
    cases G
    congr
    exact DFunLike.coe_injective hFG

/-- The underlying map of a concordance is that of its track. -/
@[simp]
theorem coe_toSmoothEmbedding (F : Concordance f g) : ⇑F.toSmoothEmbedding = F :=
  (rfl)

/-- Two concordances with the same track are equal. -/
@[ext]
theorem ext {F G : Concordance f g} (hFG : ∀ p, F p = G p) : F = G :=
  DFunLike.coe_injective (funext hFG)

variable (F : Concordance f g)

/-- A concordance is the product of its initial embedding with the identity on a positive-width
collar. -/
theorem exists_pos_apply_eq_left :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), t ≤ ε → F (x, t) = (f x, t) := by
  rcases F.exists_pos_apply_eq_left' with ⟨ε, hε, hF⟩
  exact ⟨ε, hε, fun x t ht => by simpa only [← coe_toSmoothEmbedding] using hF x t ht⟩

/-- A concordance is the product of its final embedding with the identity on a positive-width
collar. -/
theorem exists_pos_apply_eq_right :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), 1 - ε ≤ t → F (x, t) = (g x, t) := by
  rcases F.exists_pos_apply_eq_right' with ⟨ε, hε, hF⟩
  exact ⟨ε, hε, fun x t ht => by simpa only [← coe_toSmoothEmbedding] using hF x t ht⟩

/-- A concordance is the product of its initial embedding with the identity for `t ≤ 0`. -/
theorem apply_of_nonpos (x : M) {t : ℝ} (ht : t ≤ 0) : F (x, t) = (f x, t) := by
  rcases F.exists_pos_apply_eq_left with ⟨ε, hε, hF⟩
  exact hF x t (ht.trans hε.le)

/-- A concordance is the product of its final embedding with the identity for `1 ≤ t`. -/
theorem apply_of_one_le (x : M) {t : ℝ} (ht : 1 ≤ t) : F (x, t) = (g x, t) := by
  rcases F.exists_pos_apply_eq_right with ⟨ε, hε, hF⟩
  exact hF x t (by linarith)

/-- At time `0` a concordance is its initial embedding. -/
@[simp]
theorem apply_zero (x : M) : F (x, 0) = (f x, 0) :=
  F.apply_of_nonpos x le_rfl

/-- At time `1` a concordance is its final embedding. -/
@[simp]
theorem apply_one (x : M) : F (x, 1) = (g x, 1) :=
  F.apply_of_one_le x le_rfl

/-- A concordance moves no time outside the open interval `(0, 1)` and keeps times inside it, so
it preserves the comparison of time with any level `c ∉ (0, 1)`. -/
theorem snd_apply_lt_iff (x : M) {t c : ℝ} (hc : c ∉ Ioo 0 1) : (F (x, t)).2 < c ↔ t < c := by
  rcases le_or_gt t 0 with ht | ht
  · simp [F.apply_of_nonpos x ht]
  rcases le_or_gt 1 t with ht' | ht'
  · simp [F.apply_of_one_le x ht']
  have hmem : (F (x, t)).2 ∈ Ioo 0 1 := F.snd_apply_mem_Ioo' x t ⟨ht, ht'⟩
  simp only [mem_Ioo, not_and_or, not_lt] at hc hmem
  constructor <;> intro <;> rcases hc with hc | hc <;> linarith

/-- A concordance preserves the comparison of time with any level `c ∉ (0, 1)` from below. -/
theorem lt_snd_apply_iff (x : M) {t c : ℝ} (hc : c ∉ Ioo 0 1) : c < (F (x, t)).2 ↔ c < t := by
  rcases le_or_gt t 0 with ht | ht
  · simp [F.apply_of_nonpos x ht]
  rcases le_or_gt 1 t with ht' | ht'
  · simp [F.apply_of_one_le x ht']
  have hmem : (F (x, t)).2 ∈ Ioo 0 1 := F.snd_apply_mem_Ioo' x t ⟨ht, ht'⟩
  simp only [mem_Ioo, not_and_or, not_lt] at hc hmem
  constructor <;> intro <;> rcases hc with hc | hc <;> linarith

/-- A concordance maps `M × (0, 1)` into `N × (0, 1)` and nothing else there. -/
theorem snd_apply_mem_Ioo_iff (x : M) {t : ℝ} : (F (x, t)).2 ∈ Ioo 0 1 ↔ t ∈ Ioo 0 1 := by
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  simp only [mem_Ioo, F.lt_snd_apply_iff x h0, F.snd_apply_lt_iff x h1]

/-! ### Diffeomorphisms -/

section Diffeomorph

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M']
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J n P]

/-- An ambient diffeomorphism carries a concordance from `f` to `g` to one between the
transported embeddings. -/
def transDiffeomorph (F : Concordance f g) (e : N ≃ₘ^n⟮J, J⟯ P) :
    Concordance (f.transDiffeomorph e) (g.transDiffeomorph e) where
  toSmoothEmbedding :=
    F.toSmoothEmbedding.transDiffeomorph (e.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ n))
  exists_pos_apply_eq_left' := by
    rcases F.exists_pos_apply_eq_left' with ⟨ε, hε, hF⟩
    exact ⟨ε, hε, fun x t ht => by simp [hF x t ht]⟩
  exists_pos_apply_eq_right' := by
    rcases F.exists_pos_apply_eq_right with ⟨ε, hε, hF⟩
    exact ⟨ε, hε, fun x t ht => by simp [hF x t ht]⟩
  snd_apply_mem_Ioo' x t ht := by simpa using F.snd_apply_mem_Ioo' x t ht

@[simp]
theorem transDiffeomorph_apply (F : Concordance f g) (e : N ≃ₘ^n⟮J, J⟯ P) (p : M × ℝ) :
    F.transDiffeomorph e p = (e (F p).1, (F p).2) := by
  ext <;> simp [← coe_toSmoothEmbedding, transDiffeomorph]

/-- A diffeomorphism of the source reparametrizes a concordance from `f` to `g` into one between
the reparametrized embeddings. -/
def compDiffeomorph (F : Concordance f g) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    Concordance (f.compDiffeomorph e) (g.compDiffeomorph e) where
  toSmoothEmbedding :=
    F.toSmoothEmbedding.compDiffeomorph (e.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ n))
  exists_pos_apply_eq_left' := by
    rcases F.exists_pos_apply_eq_left with ⟨ε, hε, hF⟩
    exact ⟨ε, hε, fun x t ht => by simp [hF _ t ht]⟩
  exists_pos_apply_eq_right' := by
    rcases F.exists_pos_apply_eq_right with ⟨ε, hε, hF⟩
    exact ⟨ε, hε, fun x t ht => by simp [hF _ t ht]⟩
  snd_apply_mem_Ioo' x t ht := by simpa using F.snd_apply_mem_Ioo' (e x) t ht

@[simp]
theorem compDiffeomorph_apply (F : Concordance f g) (e : M' ≃ₘ^n⟮I, I⟯ M) (p : M' × ℝ) :
    F.compDiffeomorph e p = F (e p.1, p.2) := by
  simp [← coe_toSmoothEmbedding, compDiffeomorph, Prod.map]

end Diffeomorph

/-! ### Affine changes of time -/

/-- The affine diffeomorphism `t ↦ a * t + b` of the real line. -/
private def affineTime (n : ℕ∞ω) (a b : ℝ) (ha : a ≠ 0) : ℝ ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ where
  toFun t := a * t + b
  invFun s := a⁻¹ * (s - b)
  left_inv t := by field_simp; ring
  right_inv s := by field_simp; ring
  contMDiff_toFun := ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff

@[simp]
private theorem affineTime_apply (n : ℕ∞ω) (a b : ℝ) (ha : a ≠ 0) (t : ℝ) :
    affineTime n a b ha t = a * t + b :=
  (rfl)

@[simp]
private theorem affineTime_symm_apply (n : ℕ∞ω) (a b : ℝ) (ha : a ≠ 0) (s : ℝ) :
    (affineTime n a b ha).symm s = a⁻¹ * (s - b) :=
  (rfl)

variable [IsManifold I n M] [IsManifold J n N]

/-- Conjugate a smooth embedding of `M × ℝ` into `N × ℝ` by the affine change of time
`t ↦ a * t + b`. -/
private def conjTime (T : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ))
    (a b : ℝ) (ha : a ≠ 0) : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ) :=
  (T.compDiffeomorph ((Diffeomorph.refl I M n).prodCongr (affineTime n a b ha))).transDiffeomorph
    ((Diffeomorph.refl J N n).prodCongr (affineTime n a b ha).symm)

private theorem conjTime_apply
    (T : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ)) (a b : ℝ) (ha : a ≠ 0)
    (x : M) (t : ℝ) :
    conjTime T a b ha (x, t) = ((T (x, a * t + b)).1, a⁻¹ * ((T (x, a * t + b)).2 - b)) := by
  ext <;> simp [conjTime]

/-! ### The constant and the reversed concordance -/

/-- The constant concordance from `f` to itself, whose track is `f × id`. -/
def refl (f : SmoothEmbedding I J n M N) : Concordance f f where
  toSmoothEmbedding := f.prodMap SmoothEmbedding.id
  exists_pos_apply_eq_left' := ⟨1, by norm_num, by simp⟩
  exists_pos_apply_eq_right' := ⟨1, by norm_num, by simp⟩
  snd_apply_mem_Ioo' _ _ ht := by simpa using ht

@[simp]
theorem refl_apply (f : SmoothEmbedding I J n M N) (p : M × ℝ) : refl f p = (f p.1, p.2) := by
  simp [← coe_toSmoothEmbedding, refl]

/-- The reversed concordance from `g` to `f`, obtained by reflecting time in `1 / 2`. -/
def symm (F : Concordance f g) : Concordance g f where
  toSmoothEmbedding := conjTime F.toSmoothEmbedding (-1) 1 (by norm_num)
  exists_pos_apply_eq_left' := by
    rcases F.exists_pos_apply_eq_right with ⟨ε, hε, hF⟩
    refine ⟨ε, hε, fun x t ht => ?_⟩
    rw [conjTime_apply, coe_toSmoothEmbedding, hF x (-1 * t + 1) (by linarith)]
    ext <;> simp
  exists_pos_apply_eq_right' := by
    rcases F.exists_pos_apply_eq_left with ⟨ε, hε, hF⟩
    refine ⟨ε, hε, fun x t ht => ?_⟩
    rw [conjTime_apply, coe_toSmoothEmbedding, hF x (-1 * t + 1) (by linarith)]
    ext <;> simp
  snd_apply_mem_Ioo' x t ht := by
    rw [conjTime_apply, coe_toSmoothEmbedding]
    have := (F.snd_apply_mem_Ioo_iff x).2 (show -1 * t + 1 ∈ Ioo 0 1 by
      simp only [mem_Ioo] at ht ⊢; constructor <;> linarith)
    simp only [mem_Ioo] at this ⊢
    constructor <;> linarith

@[simp]
theorem symm_apply (F : Concordance f g) (x : M) (t : ℝ) :
    F.symm (x, t) = ((F (x, 1 - t)).1, 1 - (F (x, 1 - t)).2) := by
  rw [← coe_toSmoothEmbedding, symm, conjTime_apply, coe_toSmoothEmbedding,
    show -1 * t + 1 = 1 - t by ring]
  ext <;> simp

/-- Reversing a concordance twice gives it back. -/
@[simp]
theorem symm_symm (F : Concordance f g) : F.symm.symm = F := by
  ext ⟨x, t⟩ <;> simp

/-! ### Stacking concordances -/

/-- The first concordance, run at triple speed during `[0, 1/3]`. -/
private def lower (F : Concordance f g) :
    SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ) :=
  conjTime F.toSmoothEmbedding 3 0 (by norm_num)

/-- The second concordance, run at triple speed during `[2/3, 1]`. -/
private def upper (G : Concordance g h) :
    SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ) :=
  conjTime G.toSmoothEmbedding 3 (-2) (by norm_num)

private theorem lower_apply (F : Concordance f g) (x : M) (t : ℝ) :
    lower F (x, t) = ((F (x, 3 * t)).1, (F (x, 3 * t)).2 / 3) := by
  rw [lower, conjTime_apply, coe_toSmoothEmbedding, add_zero, sub_zero, inv_mul_eq_div]

private theorem upper_apply (G : Concordance g h) (x : M) (t : ℝ) :
    upper G (x, t) = ((G (x, 3 * t - 2)).1, ((G (x, 3 * t - 2)).2 + 2) / 3) := by
  rw [upper, conjTime_apply, coe_toSmoothEmbedding, sub_neg_eq_add, inv_mul_eq_div,
    ← sub_eq_add_neg]

/-- The stacked track: the first concordance until time `1 / 2`, the second one afterwards.
Both are the product `g × id` during `[1/3, 2/3]`. -/
private def stack (F : Concordance f g) (G : Concordance g h) (p : M × ℝ) : N × ℝ :=
  if p.2 ≤ 1 / 2 then lower F p else upper G p

private theorem stack_eqOn_lower (F : Concordance f g) (G : Concordance g h) :
    EqOn (stack F G) (lower F) {p | p.2 < 2 / 3} := by
  rintro ⟨x, t⟩ (ht : t < 2 / 3)
  by_cases ht' : t ≤ 1 / 2
  · simp only [stack, ht', ↓reduceIte]
  simp only [stack, ht', ↓reduceIte]
  rw [lower_apply, upper_apply, F.apply_of_one_le x (by linarith),
    G.apply_of_nonpos x (by linarith)]
  ext <;> simp

private theorem stack_eqOn_upper (F : Concordance f g) (G : Concordance g h) :
    EqOn (stack F G) (upper G) {p | 1 / 3 < p.2} := by
  rintro ⟨x, t⟩ (ht : 1 / 3 < t)
  by_cases ht' : t ≤ 1 / 2
  · simp only [stack, ht', ↓reduceIte]
    rw [lower_apply, upper_apply, F.apply_of_one_le x (by linarith),
      G.apply_of_nonpos x (by linarith)]
    ext <;> simp
  · simp only [stack, ht', ↓reduceIte]

private theorem snd_stack_lt_iff (F : Concordance f g) (G : Concordance g h) (p : M × ℝ) :
    (stack F G p).2 < 2 / 3 ↔ p.2 < 2 / 3 := by
  obtain ⟨x, t⟩ := p
  have h2 : (2 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.2]
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
  by_cases ht : t ≤ 1 / 2
  · simp only [stack, ht, ↓reduceIte, lower_apply]
    have key := F.snd_apply_lt_iff x (t := 3 * t) h2
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]
  · simp only [stack, ht, ↓reduceIte, upper_apply]
    have key := G.snd_apply_lt_iff x (t := 3 * t - 2) h0
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]

private theorem lt_snd_stack_iff (F : Concordance f g) (G : Concordance g h) (p : M × ℝ) :
    1 / 3 < (stack F G p).2 ↔ 1 / 3 < p.2 := by
  obtain ⟨x, t⟩ := p
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  have hm1 : (-1 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.1]
  by_cases ht : t ≤ 1 / 2
  · simp only [stack, ht, ↓reduceIte, lower_apply]
    have key := F.lt_snd_apply_iff x (t := 3 * t) h1
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]
  · simp only [stack, ht, ↓reduceIte, upper_apply]
    have key := G.lt_snd_apply_iff x (t := 3 * t - 2) hm1
    constructor
    · intro hlt; linarith [key.1 (by linarith)]
    · intro hlt; linarith [key.2 (by linarith)]

private theorem isSmoothEmbedding_stack [FiniteDimensional ℝ E'] (F : Concordance f g)
    (G : Concordance g h) :
    IsSmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (stack F G) := by
  have hlow : IsOpen {p : M × ℝ | p.2 < 2 / 3} := isOpen_lt continuous_snd continuous_const
  have hup : IsOpen {p : M × ℝ | 1 / 3 < p.2} := isOpen_lt continuous_const continuous_snd
  have himm : IsImmersion (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (stack F G) := by
    refine isImmersion_iff_forall_isImmersionAt.2 fun p => ?_
    rcases lt_or_ge p.2 (2 / 3) with hp | hp
    · exact ((lower F).isImmersion.isImmersionAt p).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hlow.mem_nhds hp) (stack_eqOn_lower F G).symm)
    · exact ((upper G).isImmersion.isImmersionAt p).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hup.mem_nhds (lt_of_lt_of_le (by norm_num) hp))
          (stack_eqOn_upper F G).symm)
  refine ⟨himm, ?_⟩
  -- The two open slabs `{s < 2 / 3}` and `{1 / 3 < s}` cover `N × ℝ`; over each the stacked
  -- track is one of the two rescaled tracks, restricted to the matching slab of `M × ℝ`.
  let U : Bool → TopologicalSpace.Opens (N × ℝ) := fun b => bif b
    then ⟨{q | 1 / 3 < q.2}, isOpen_lt continuous_const continuous_snd⟩
    else ⟨{q | q.2 < 2 / 3}, isOpen_lt continuous_snd continuous_const⟩
  let W : Bool → Set (M × ℝ) := fun b => bif b then {p | 1 / 3 < p.2} else {p | p.2 < 2 / 3}
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range (stack F G) himm.contMDiff.continuous
    U ?_ (fun b => W b) (fun b => Subtype.val) (fun b => continuous_subtype_val) ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    rcases lt_or_ge (stack F G p).2 (2 / 3) with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, (by linarith : 1 / 3 < (stack F G p).2)⟩
  · rintro (_ | _) p hp
    · exact ⟨⟨p, (snd_stack_lt_iff F G p).1 hp⟩, rfl⟩
    · exact ⟨⟨p, (lt_snd_stack_iff F G p).1 hp⟩, rfl⟩
  · rintro (_ | _)
    · have heq : stack F G ∘ (Subtype.val : W false → M × ℝ) = lower F ∘ Subtype.val :=
        funext fun p => stack_eqOn_lower F G p.2
      rw [heq]
      exact (lower F).isEmbedding.comp IsEmbedding.subtypeVal
    · have heq : stack F G ∘ (Subtype.val : W true → M × ℝ) = upper G ∘ Subtype.val :=
        funext fun p => stack_eqOn_upper F G p.2
      rw [heq]
      exact (upper G).isEmbedding.comp IsEmbedding.subtypeVal

/-- The stacked concordance from `f` to `h`: the concordance `F` from `f` to `g` at triple speed
during `[0, 1/3]`, then the constant concordance at `g`, then the concordance `G` from `g` to `h`
at triple speed during `[2/3, 1]`. -/
def trans [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h) :
    Concordance f h where
  toSmoothEmbedding := .ofIsSmoothEmbedding (stack F G) (isSmoothEmbedding_stack F G)
  exists_pos_apply_eq_left' := by
    rcases F.exists_pos_apply_eq_left with ⟨ε, hε, hF⟩
    let δ := min (ε / 3) (1 / 4)
    refine ⟨δ, lt_min (by linarith) (by norm_num), fun x t ht => ?_⟩
    have hδε : δ ≤ ε / 3 := min_le_left _ _
    have hδ : δ ≤ 1 / 4 := min_le_right _ _
    have ht' : t ≤ 1 / 2 := by linarith
    rw [ofIsSmoothEmbedding_apply]
    simp only [stack, ht', ↓reduceIte, lower_apply]
    rw [hF x (3 * t) (by linarith)]
    ext <;> simp
  exists_pos_apply_eq_right' := by
    rcases G.exists_pos_apply_eq_right with ⟨ε, hε, hG⟩
    let δ := min (ε / 3) (1 / 4)
    refine ⟨δ, lt_min (by linarith) (by norm_num), fun x t ht => ?_⟩
    have hδε : δ ≤ ε / 3 := min_le_left _ _
    have hδ : δ ≤ 1 / 4 := min_le_right _ _
    have ht' : ¬ t ≤ 1 / 2 := by linarith
    rw [ofIsSmoothEmbedding_apply]
    simp only [stack, ht', ↓reduceIte, upper_apply]
    rw [hG x (3 * t - 2) (by linarith)]
    ext <;> simp
  snd_apply_mem_Ioo' x t ht := by
    rw [ofIsSmoothEmbedding_apply]
    have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
    have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
    have h3 : (3 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.2]
    have hm2 : (-2 : ℝ) ∉ Ioo 0 1 := fun h => by linarith [h.1]
    simp only [mem_Ioo] at ht ⊢
    by_cases ht' : t ≤ 1 / 2
    · simp only [stack, ht', ↓reduceIte, lower_apply]
      have hlo := F.lt_snd_apply_iff x (t := 3 * t) h0
      have hhi := F.snd_apply_lt_iff x (t := 3 * t) h3
      constructor <;> linarith [hlo.2 (by linarith), hhi.2 (by linarith)]
    · simp only [stack, ht', ↓reduceIte, upper_apply]
      have hlo := G.lt_snd_apply_iff x (t := 3 * t - 2) hm2
      have hhi := G.snd_apply_lt_iff x (t := 3 * t - 2) h1
      constructor <;> linarith [hlo.2 (by linarith), hhi.2 (by linarith)]

private theorem trans_apply_eq_stack [FiniteDimensional ℝ E'] (F : Concordance f g)
    (G : Concordance g h) (p : M × ℝ) : F.trans G p = stack F G p :=
  ofIsSmoothEmbedding_apply _ _ p

/-- Before time `1 / 2` the stacked concordance runs the first concordance at triple speed. -/
theorem trans_apply_of_le [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h)
    (x : M) {t : ℝ} (ht : t ≤ 1 / 2) :
    F.trans G (x, t) = ((F (x, 3 * t)).1, (F (x, 3 * t)).2 / 3) := by
  rw [trans_apply_eq_stack]
  simp only [stack, ht, ↓reduceIte, lower_apply]

/-- After time `1 / 2` the stacked concordance runs the second concordance at triple speed. -/
theorem trans_apply_of_lt [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h)
    (x : M) {t : ℝ} (ht : 1 / 2 < t) :
    F.trans G (x, t) = ((G (x, 3 * t - 2)).1, ((G (x, 3 * t - 2)).2 + 2) / 3) := by
  rw [trans_apply_eq_stack]
  simp only [stack, not_le.2 ht, ↓reduceIte, upper_apply]

/-! ### Diffeotopies -/


/-- The time reparametrization of a diffeotopy trace: `Real.smoothTransition`, as a map into the
unit interval. -/
private def smoothTransitionUnit (t : ℝ) : unitInterval :=
  ⟨Real.smoothTransition t, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

private theorem contMDiff_smoothTransitionUnit (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n smoothTransitionUnit := by
  refine contMDiff_iff_comp_subtypeVal_Icc.2 ⟨?_, ?_⟩
  · exact Real.smoothTransition.continuous.subtype_mk _
  · exact (Real.smoothTransition.contDiff.of_le hn).contMDiff

/-- A smooth transition which is constant on neighborhoods of both ends of the unit interval. -/
private def collaredSmoothTransitionUnit (t : ℝ) : unitInterval :=
  smoothTransitionUnit (2 * t - 1 / 2)

private theorem contMDiff_collaredSmoothTransitionUnit (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n collaredSmoothTransitionUnit :=
  (contMDiff_smoothTransitionUnit hn).comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff)

/-- The diffeomorphism `(y, t) ↦ (Φ (ρ t, y), t)` of `N × ℝ`, where `ρ` is the smooth transition
from `0` to `1`. -/
private def traceDiffeomorph (Φ : Diffeotopy J n N) (hn : n ≤ ∞) :
    (N × ℝ) ≃ₘ^n⟮J.prod 𝓘(ℝ), J.prod 𝓘(ℝ)⟯ (N × ℝ) where
  toFun p := (Φ (collaredSmoothTransitionUnit p.2, p.1), p.2)
  invFun p := ((Φ.toDiffeomorph.symm (collaredSmoothTransitionUnit p.2, p.1)).2, p.2)
  left_inv p := by
    set q := (collaredSmoothTransitionUnit p.2, p.1)
    have hp : (q.1, (Φ.toDiffeomorph q).2) = Φ.toDiffeomorph q := (Φ.toDiffeomorph_apply q).symm
    ext
    · simp only [Diffeotopy.coe_apply]
      rw [hp, Φ.toDiffeomorph.symm_apply_apply]
    · rfl
  right_inv p := by
    set q := (collaredSmoothTransitionUnit p.2, p.1)
    have hp : (q.1, (Φ.toDiffeomorph.symm q).2) = Φ.toDiffeomorph.symm q :=
      (Φ.toDiffeomorph_symm_apply q).symm
    ext
    · simp only [Diffeotopy.coe_apply]
      rw [hp, Φ.toDiffeomorph.apply_symm_apply]
    · rfl
  contMDiff_toFun :=
    (Φ.contMDiff.comp (((contMDiff_collaredSmoothTransitionUnit hn).comp contMDiff_snd).prodMk
      contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (contMDiff_snd.comp (Φ.toDiffeomorph.symm.contMDiff.comp
      (((contMDiff_collaredSmoothTransitionUnit hn).comp contMDiff_snd).prodMk
        contMDiff_fst))).prodMk contMDiff_snd

omit [IsManifold J n N] in
@[simp]
private theorem traceDiffeomorph_apply (Φ : Diffeotopy J n N) (hn : n ≤ ∞) (p : N × ℝ) :
    traceDiffeomorph Φ hn p = (Φ (collaredSmoothTransitionUnit p.2, p.1), p.2) :=
  (rfl)

/-- The **trace of a diffeotopy** `Φ` of `N`: the concordance `(x, t) ↦ (Φ (ρ t, f x), t)` from `f`
to its image under the final diffeomorphism of `Φ`, where
`ρ(t) = Real.smoothTransition (2 * t - 1 / 2)`. -/
def ofDiffeotopy (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (f : SmoothEmbedding I J n M N) :
    Concordance f (f.transDiffeomorph Φ.final) where
  toSmoothEmbedding := (f.prodMap SmoothEmbedding.id).transDiffeomorph (traceDiffeomorph Φ hn)
  exists_pos_apply_eq_left' := by
    refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
    have : collaredSmoothTransitionUnit t = 0 :=
      Subtype.ext (Real.smoothTransition.zero_of_nonpos (by linarith))
    simp [this]
  exists_pos_apply_eq_right' := by
    refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
    have : collaredSmoothTransitionUnit t = 1 :=
      Subtype.ext (Real.smoothTransition.one_of_one_le (by linarith))
    simp [this, Diffeotopy.final_apply]
  snd_apply_mem_Ioo' _ _ ht := by simpa using ht

@[simp]
theorem ofDiffeotopy_apply (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (f : SmoothEmbedding I J n M N)
    (p : M × ℝ) :
    ofDiffeotopy hn Φ f p =
      (Φ (⟨Real.smoothTransition (2 * p.2 - 1 / 2), Real.smoothTransition.nonneg _,
        Real.smoothTransition.le_one _⟩, f p.1), p.2) := by
  simp [← coe_toSmoothEmbedding, ofDiffeotopy, collaredSmoothTransitionUnit,
    smoothTransitionUnit]

end Concordance

/-! ### The concordance relation -/

namespace Concordant

variable {f g h : SmoothEmbedding I J n M N}

/-- A concordance witnesses concordance. -/
theorem of_concordance (F : Concordance f g) : Concordant f g :=
  ⟨F⟩

variable [IsManifold I n M] [IsManifold J n N]

/-- Concordance is reflexive. -/
@[refl]
theorem refl (f : SmoothEmbedding I J n M N) : Concordant f f :=
  ⟨Concordance.refl f⟩

/-- Concordance is symmetric. -/
@[symm]
theorem symm (hfg : Concordant f g) : Concordant g f :=
  hfg.map Concordance.symm

/-- Concordance is transitive, for a finite-dimensional ambient model. -/
@[trans]
theorem trans [FiniteDimensional ℝ E'] (hfg : Concordant f g) (hgh : Concordant g h) :
    Concordant f h :=
  hfg.elim fun F => hgh.elim fun G => ⟨F.trans G⟩

/-- For a finite-dimensional ambient model, concordance is an equivalence relation on smooth
embeddings. -/
theorem equivalence [FiniteDimensional ℝ E'] :
    Equivalence (Concordant (I := I) (J := J) (n := n) (M := M) (N := N)) :=
  ⟨refl, symm, trans⟩

/-- Concordance of smooth embeddings, packaged as a setoid. -/
def setoid [FiniteDimensional ℝ E'] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (n : ℕ∞ω) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J n N] :
    Setoid (SmoothEmbedding I J n M N) where
  r := Concordant
  iseqv := equivalence

/-- The relation of the concordance setoid is concordance. -/
@[simp]
theorem setoid_r_iff [FiniteDimensional ℝ E'] : (setoid I J n M N).r f g ↔ Concordant f g :=
  Iff.rfl

end Concordant

/-- Smoothly ambient isotopic embeddings are concordant, through the trace of the diffeotopy. -/
theorem SmoothAmbientIsotopic.concordant [IsManifold I n M] [IsManifold J n N] (hn : n ≤ ∞)
    {f g : SmoothEmbedding I J n M N} (hfg : SmoothAmbientIsotopic f g) : Concordant f g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  have hg : f.transDiffeomorph Φ.final = g := SmoothEmbedding.ext fun x => by simp [hΦ x]
  exact hg ▸ ⟨Concordance.ofDiffeotopy hn Φ f⟩

end SmoothEmbedding

end TauCeti
