/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import TauCeti.Analysis.Convex.Conjugate

/-!
# The Fenchel–Moreau theorem

Let `E` be a real locally convex topological vector space and let `f : E → EReal` be convex
(its real epigraph `{(x, r) | f x ≤ r}` is convex), lower semicontinuous, and never `⊥`. This file
proves that such an `f` is the pointwise supremum of the continuous affine functions below it:
for every `x₀` and every real `t < f x₀` there is a continuous linear functional `ℓ` and a real
`c` with `ℓ + c ≤ f` everywhere and `ℓ x₀ + c = t`. The value `f x₀ = ⊤` is allowed, and no
point of the effective domain is singled out: this is the extended-valued form of Mathlib's
`ConvexOn.exists_affine_le_of_lt`, which treats real-valued functions on a closed convex set.

For a pairing `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` that represents every continuous linear functional on `E`,
each such affine minorant is `x ↦ B x y + c`, and each affine minorant lies below the
biconjugate `f⋆⋆`. Together with the algebraic inequality `f⋆⋆ ≤ f`, this gives the
**Fenchel–Moreau theorem** `f⋆⋆ = f`. If moreover every functional `x ↦ B x y` is continuous
(that is, the topology of `E` is compatible with the pairing), the equality characterises the
functions it applies to: `f⋆⋆ = f` holds exactly when `f` is convex and lower semicontinuous and
either never takes the value `⊥` or is identically `⊥`. Neither a Hausdorff hypothesis on `E`
nor any topology on `F` is needed. For a complete real inner product space the inner product
represents every continuous linear functional (the Fréchet–Riesz theorem), which gives the
self-dual form used in Euclidean optimal transport.

## Main statements

* `TauCeti.exists_affine_le_of_lt` — a convex lower-semicontinuous function
  `f : E → EReal` that is never `⊥` has, below every real `t < f x₀`, a continuous affine minorant
  taking the value `t` at `x₀`;
* `TauCeti.fenchelConjugate_flip_fenchelConjugate_eq` — **the Fenchel–Moreau theorem**
  `f⋆⋆ = f` for a pairing representing the continuous dual of `E`, and
  `TauCeti.fenchelConjugate_flip_fenchelConjugate_eq_iff`, its converse for a compatible
  topology;
* `TauCeti.fenchelConjugate_innerₗ_fenchelConjugate_innerₗ` — the Fenchel–Moreau theorem on a
  complete real inner product space.

## Implementation notes

The affine minorant is obtained by separating the point `(x₀, t)` from the closed convex real
epigraph of `f` in `E × ℝ` with `geometric_hahn_banach_point_closed`. The separating functional
has the form `(x, r) ↦ ℓ x + a * r`. When `a > 0` it is non-vertical and yields the minorant at
once. This is always the case when `f x₀` is finite. When `f x₀ = ⊤` the hyperplane may be
vertical (`a = 0`); then `f` is either identically `⊤`, or it has a non-vertical minorant
through a point of its effective domain, and adding a large multiple of the vertical separator
to that minorant lifts it above `t` at `x₀`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 12.1 and
  Corollary 12.2.1.
* I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, Classics in Applied
  Mathematics 28, SIAM 1999, Chapter I, Proposition 3.1 and Proposition 4.1.
* H. H. Bauschke and P. L. Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert
  Spaces*, CMS Books in Mathematics, Springer 2011, Theorem 13.32.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {f : E → EReal}

/-- Separation of a point strictly below the graph of a convex lower-semicontinuous function from
its real epigraph, with the separating functional on `E × ℝ` written as `(x, r) ↦ ℓ x + r * a`. -/
private theorem exists_separation_epigraph (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous f) {x₀ : E} {t : ℝ} (ht : (t : EReal) < f x₀) :
    ∃ (ℓ : E →L[ℝ] ℝ) (a u : ℝ), ℓ x₀ + t * a < u ∧
      ∀ x (r : ℝ), f x ≤ r → u < ℓ x + r * a := by
  -- The real epigraph is the preimage of the closed extended-real epigraph.
  have hclosed : IsClosed {p : E × ℝ | f p.1 ≤ p.2} :=
    hlsc.isClosed_epigraph.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp
      continuous_snd))
  obtain ⟨φ, u, hx₀, hepi⟩ := geometric_hahn_banach_point_closed hf hclosed
    (x := (x₀, t)) (not_le.2 ht)
  have hφ (x : E) (r : ℝ) : φ (x, r) = φ.comp (ContinuousLinearMap.inl ℝ E ℝ) x + r * φ (0, 1) := by
    have hxr : ((x, r) : E × ℝ) = (x, 0) + r • ((0 : E), (1 : ℝ)) := by simp
    rw [hxr, map_add, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
  refine ⟨φ.comp (ContinuousLinearMap.inl ℝ E ℝ), φ (0, 1), u, ?_, fun x r hxr => ?_⟩
  · rw [← hφ]
    exact hx₀
  · rw [← hφ]
    exact hepi (x, r) hxr

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- A separating functional whose epigraph side contains a point above the separated point is
non-vertical, and it yields a continuous affine minorant of `f` exceeding `t` at `x₀`. -/
private theorem exists_lt_of_separation (hbot : ∀ x, f x ≠ ⊥) {x₀ : E} {t : ℝ} {ℓ : E →L[ℝ] ℝ}
    {a u : ℝ} (ha : 0 < a) (hx₀ : ℓ x₀ + t * a < u)
    (hepi : ∀ x (r : ℝ), f x ≤ r → u < ℓ x + r * a) :
    ∃ (ℓ' : E →L[ℝ] ℝ) (c : ℝ), (∀ x, ((ℓ' x + c : ℝ) : EReal) ≤ f x) ∧ t < ℓ' x₀ + c := by
  have hval (x : E) : ((-a⁻¹) • ℓ) x + u / a = (u - ℓ x) / a := by
    rw [smul_apply, smul_eq_mul, neg_mul, ← sub_eq_neg_add, inv_mul_eq_div, div_sub_div_same]
  refine ⟨(-a⁻¹) • ℓ, u / a, fun x => ?_, ?_⟩
  · induction hfx : f x with
    | bot => exact absurd hfx (hbot x)
    | top => exact le_top
    | coe r =>
      have hr := hepi x r (le_of_eq hfx)
      rw [EReal.coe_le_coe_iff, hval, div_le_iff₀ ha]
      linarith
  · rw [hval, lt_div_iff₀ ha]
    linarith

/-- At a point where `f` is finite, every real `t < f x₀` is exceeded at `x₀` by a continuous
affine minorant of `f`. -/
private theorem exists_lt_of_lt_of_ne_top (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous f) (hbot : ∀ x, f x ≠ ⊥) {x₀ : E} {t : ℝ}
    (ht : (t : EReal) < f x₀) (htop : f x₀ ≠ ⊤) :
    ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ), (∀ x, ((ℓ x + c : ℝ) : EReal) ≤ f x) ∧ t < ℓ x₀ + c := by
  obtain ⟨ℓ, a, u, hx₀, hepi⟩ := exists_separation_epigraph hf hlsc ht
  refine exists_lt_of_separation hbot ?_ hx₀ hepi
  -- The point `(x₀, f x₀)` lies on the epigraph side, strictly above `(x₀, t)`.
  have hr := hepi x₀ (f x₀).toReal (EReal.le_coe_toReal htop)
  have htr : t < (f x₀).toReal := by
    rw [← EReal.coe_toReal htop (hbot x₀)] at ht
    exact EReal.coe_lt_coe_iff.1 ht
  by_contra! ha
  linarith [mul_le_mul_of_nonpos_right htr.le ha]

/-- **Continuous affine minorants of a convex lower-semicontinuous function.** On a real locally
convex space, let `f : E → EReal` have convex real epigraph, be lower semicontinuous and never
take the value `⊥`. For every point `x₀` and every real `t < f x₀` (including the case
`f x₀ = ⊤`) there are a continuous linear functional `ℓ` and a real `c` such that `ℓ + c` lies
below `f` everywhere and takes the value `t` at `x₀`. Consequently `f` is the pointwise supremum
of its continuous affine minorants. -/
theorem exists_affine_le_of_lt (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous f) (hbot : ∀ x, f x ≠ ⊥) {x₀ : E} {t : ℝ}
    (ht : (t : EReal) < f x₀) :
    ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ), (∀ x, ((ℓ x + c : ℝ) : EReal) ≤ f x) ∧ ℓ x₀ + c = t := by
  -- It suffices to find a minorant exceeding `t` at `x₀`, then lower its constant term.
  suffices h : ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ), (∀ x, ((ℓ x + c : ℝ) : EReal) ≤ f x) ∧ t < ℓ x₀ + c by
    obtain ⟨ℓ, c, hle, hlt⟩ := h
    refine ⟨ℓ, t - ℓ x₀, fun x => le_trans ?_ (hle x), by ring⟩
    exact EReal.coe_le_coe_iff.2 (by linarith)
  rcases ne_or_eq (f x₀) ⊤ with htop | _
  · exact exists_lt_of_lt_of_ne_top hf hlsc hbot ht htop
  by_cases hdom : ∀ x, f x = ⊤
  · exact ⟨0, t + 1, fun x => by simp [hdom x], by simp⟩
  -- `f` is finite at some `x₁`, so it has an affine minorant `ℓ₁ + c₁`.
  obtain ⟨x₁, hx₁⟩ := not_forall.1 hdom
  obtain ⟨ℓ₁, c₁, hle₁, -⟩ := exists_lt_of_lt_of_ne_top hf hlsc hbot
    (t := (f x₁).toReal - 1)
    ((EReal.coe_lt_coe_iff.2 (sub_one_lt _)).trans_eq (EReal.coe_toReal hx₁ (hbot x₁))) hx₁
  obtain ⟨ℓ, a, u, hx₀, hepi⟩ := exists_separation_epigraph hf hlsc ht
  rcases lt_or_ge 0 a with ha | ha
  · exact exists_lt_of_separation hbot ha hx₀ hepi
  -- The separator cannot slope downwards: on the vertical ray above `x₁` it would fall below `u`.
  have ha0 : a = 0 := by
    refine le_antisymm ha (not_lt.1 fun ha' => ?_)
    set r₁ := (f x₁).toReal
    set s := |ℓ x₁ + r₁ * a - u| + 1
    have hR : (r₁ + s / -a) * a = r₁ * a - s := by
      rw [add_mul, div_neg, neg_mul, div_mul_cancel₀ _ ha'.ne, sub_eq_add_neg]
    have hr := hepi x₁ (r₁ + s / -a) ((EReal.le_coe_toReal hx₁).trans
      (EReal.coe_le_coe_iff.2 (le_add_of_nonneg_right (div_nonneg (by positivity)
        (neg_nonneg.2 ha'.le)))))
    rw [hR] at hr
    linarith [le_abs_self (ℓ x₁ + r₁ * a - u)]
  subst ha0
  simp only [mul_zero, add_zero] at hx₀ hepi
  -- The vertical separator `u - ℓ` is negative on the effective domain and positive at `x₀`;
  -- adding a large multiple of it to `ℓ₁ + c₁` keeps a minorant and lifts it above `t` at `x₀`.
  have hpos : 0 < u - ℓ x₀ := sub_pos.2 hx₀
  set k := (|t - (ℓ₁ x₀ + c₁)| + 1) / (u - ℓ x₀)
  have hk : 0 ≤ k := div_nonneg (by positivity) hpos.le
  refine ⟨ℓ₁ - k • ℓ, c₁ + k * u, fun x => ?_, ?_⟩
  · rcases eq_or_ne (f x) ⊤ with hx | hx
    · rw [hx]
      exact le_top
    have hux : u < ℓ x := hepi x (f x).toReal (EReal.le_coe_toReal hx)
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hle₁ x)
    simp only [sub_apply, smul_apply, smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left hux.le hk]
  · simp only [sub_apply, smul_apply, smul_eq_mul]
    have hku : k * (u - ℓ x₀) = |t - (ℓ₁ x₀ + c₁)| + 1 := div_mul_cancel₀ _ hpos.ne'
    linarith [le_abs_self (t - (ℓ₁ x₀ + c₁))]

section Pairing

variable {F : Type*} [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The Fenchel–Moreau theorem.** Let the pairing `B` represent every continuous linear
functional on the locally convex space `E`. If `f : E → EReal` has convex real epigraph, is lower
semicontinuous and never takes the value `⊥`, then `f` equals its biconjugate `f⋆⋆`, the second
conjugate being taken for the transposed pairing. -/
theorem fenchelConjugate_flip_fenchelConjugate_eq (hB : ∀ ℓ : E →L[ℝ] ℝ, ∃ y, ∀ x, B x y = ℓ x)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hlsc : LowerSemicontinuous f)
    (hbot : ∀ x, f x ≠ ⊥) : fenchelConjugate B.flip (fenchelConjugate B f) = f := by
  refine le_antisymm (fenchelConjugate_flip_fenchelConjugate_le B f) fun x₀ => ?_
  refine EReal.ge_of_forall_gt_iff_ge.1 fun t ht => ?_
  obtain ⟨ℓ, c, hle, hx₀⟩ := exists_affine_le_of_lt hf hlsc hbot ht
  obtain ⟨y, hy⟩ := hB ℓ
  rw [← hx₀, ← hy]
  exact coe_add_le_fenchelConjugate_flip_fenchelConjugate B (fun x => (hy x).symm ▸ hle x) x₀

/-- **The Fenchel–Moreau theorem, with its converse.** For a pairing `B` that represents every
continuous linear functional on `E` and makes every functional `x ↦ B x y` continuous, a function
`f : E → EReal` equals its biconjugate exactly when it has convex real epigraph, is lower
semicontinuous, and either never takes the value `⊥` or is identically `⊥`. -/
theorem fenchelConjugate_flip_fenchelConjugate_eq_iff
    (hB : ∀ ℓ : E →L[ℝ] ℝ, ∃ y, ∀ x, B x y = ℓ x) (hBc : ∀ y, Continuous fun x => B x y) :
    fenchelConjugate B.flip (fenchelConjugate B f) = f ↔
      Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ LowerSemicontinuous f ∧
        ((∀ x, f x ≠ ⊥) ∨ f = ⊥) := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨hf, hlsc, hbot⟩ => ?_⟩
  · rw [← h]
    exact convex_epigraph_fenchelConjugate B.flip _
  · rw [← h]
    exact lowerSemicontinuous_fenchelConjugate B.flip hBc _
  · -- If `f x = ⊥` somewhere then `f⋆ ≡ ⊤`, so `f = f⋆⋆ ≡ ⊥`.
    refine or_iff_not_imp_left.2 fun hne => ?_
    obtain ⟨x, hx⟩ := not_forall_not.1 hne
    rw [← h, funext (fenchelConjugate_eq_top_of_eq_bot B hx)]
    exact funext (fenchelConjugate_top B.flip)
  · rcases hbot with hbot | rfl
    · exact fenchelConjugate_flip_fenchelConjugate_eq hB hf hlsc hbot
    · exact le_antisymm (fenchelConjugate_flip_fenchelConjugate_le B ⊥) bot_le

end Pairing

/-- **The Fenchel–Moreau theorem on a complete real inner product space.** A function
`f : G → EReal` with convex real epigraph that is lower semicontinuous and never takes the value
`⊥` is the conjugate of its conjugate for the inner product pairing. -/
theorem fenchelConjugate_innerₗ_fenchelConjugate_innerₗ {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] {f : G → EReal}
    (hf : Convex ℝ {p : G × ℝ | f p.1 ≤ p.2}) (hlsc : LowerSemicontinuous f)
    (hbot : ∀ x, f x ≠ ⊥) :
    fenchelConjugate (innerₗ G) (fenchelConjugate (innerₗ G) f) = f := by
  have h := fenchelConjugate_flip_fenchelConjugate_eq (B := innerₗ G) (fun ℓ =>
    ⟨(InnerProductSpace.toDual ℝ G).symm ℓ, fun x => by
      rw [innerₗ_apply_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]⟩) hf hlsc hbot
  rwa [flip_innerₗ] at h

end TauCeti
