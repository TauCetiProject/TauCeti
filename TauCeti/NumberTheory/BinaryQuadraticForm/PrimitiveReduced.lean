/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction

/-!
# Primitive reduced forms

Every positive definite integral binary quadratic form of discriminant `-D` is properly
equivalent to exactly one reduced form
(`TauCeti.BinaryQuadraticForm.orbit_mk_reducedForms_bijective`).
Primitivity is invariant under proper equivalence, so restricting to primitive forms on both sides
keeps the bijection: the primitive reduced forms of discriminant `-D` represent the proper
equivalence classes of primitive positive definite forms, `PosDefProperClass D`, each exactly once.

The finite set `TauCeti.primitiveReducedForms D` is a filter of the decidable set
`TauCeti.reducedForms D`, so the kernel can evaluate it. Its cardinality is the unweighted number of
proper classes of primitive positive definite forms, in contrast with the weighted count of all
classes recorded by `TauCeti.hurwitzClassNumber`.

The two counts are related by splitting off the content. A positive multiple `g • f` is reduced
exactly when `f` is, so a reduced form of discriminant `-D` is `g • f` for a unique `g ≥ 1` with
`g² ∣ D` and a unique primitive reduced form `f` of discriminant `-D / g²`. A primitive reduced
form has weight `1` except for `x² + y²` and `x² + x y + y²`, the only primitive reduced forms
of discriminant `-4` and `-3`. Hence the weighted count of the primitive reduced forms of
discriminant `-n` is `2 h / w`, where `h` is their number and `w` is `6`, `4` or `2` as `n = 3`,
`n = 4` or otherwise, and
```
H(D) = ∑_{g² ∣ D} 2 h(D / g²) / w(D / g²).
```
For `n ≡ 0, 3 (mod 4)`, `h` and `w` are the orders of the Picard group and of the unit group of
the quadratic order of discriminant `-n`.

## Main definitions and results

* `TauCeti.primitiveReducedForms D`: the primitive reduced forms of discriminant `-D`.
* `TauCeti.mem_primitiveReducedForms`: membership is being primitive and reduced of discriminant
  `-D`.
* `TauCeti.BinaryQuadraticForm.posDefProperClass_mk_primitiveReducedForms_bijective`: the primitive
  reduced forms represent the proper classes of primitive positive definite forms, each exactly
  once.
* `TauCeti.BinaryQuadraticForm.nat_card_posDefProperClass`: so there are
  `#(primitiveReducedForms D)` such classes, and finitely many of them.
* `TauCeti.BinaryQuadraticForm.sum_reducedForms_eq_sum_sum_primitiveReducedForms`: a sum over
  the reduced forms of discriminant `-D` is a sum over the `g` with `g² ∣ D` and the primitive
  reduced forms `f` of discriminant `-D / g²` of the summand at `g • f`.
* `TauCeti.BinaryQuadraticForm.sum_reducedFormWeight_primitiveReducedForms`: the weighted count of
  the primitive reduced forms of discriminant `-n` is `2 h / w`.
* `TauCeti.hurwitzClassNumber_eq_sum_card_primitiveReducedForms`: the Hurwitz class number is
  `∑_{g² ∣ D} 2 h(D / g²) / w(D / g²)`.

## Implementation notes

`TauCeti.primitiveReducedForms` filters by the gcd of the coefficients rather than by
`TauCeti.BinaryQuadraticForm.IsPrimitive`, whose definition is not exposed, so that the kernel can
still evaluate the set. `TauCeti.mem_primitiveReducedForms` restates membership with `IsPrimitive`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
* D. A. Cox, *Primes of the Form x² + ny²*, §2, Theorem 2.8.
* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975), for `H(D) = ∑_{g² ∣ D} 2 h(D / g²) / w(D / g²)`.
-/

public section

open Finset MulAction
open scoped MatrixGroups

namespace TauCeti

/-- The primitive reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D`: the reduced
forms whose coefficients have gcd one. For `D ≠ 0`, `mem_primitiveReducedForms` characterises
membership by `BinaryQuadraticForm.IsPrimitive`. -/
@[expose] def primitiveReducedForms (D : ℕ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ reducedForms D | Int.gcd f.a (Int.gcd f.b f.c) = 1}

/-- **The primitive reduced forms of discriminant `-D`**: for `D ≠ 0`, `f` lies in
`primitiveReducedForms D` exactly when `f.discrim = -D`, `f` is reduced, and `f` is primitive. -/
@[simp] theorem mem_primitiveReducedForms {D : ℕ} (hD : D ≠ 0) {f : BinaryQuadraticForm ℤ} :
    f ∈ primitiveReducedForms D ↔ f.discrim = -D ∧ IsReducedForm f ∧ f.IsPrimitive := by
  rw [primitiveReducedForms, mem_filter, mem_reducedForms hD, BinaryQuadraticForm.isPrimitive_iff,
    BinaryQuadraticForm.content_def, and_assoc]

/-- The primitive reduced forms are among the reduced forms. -/
theorem primitiveReducedForms_subset_reducedForms (D : ℕ) :
    primitiveReducedForms D ⊆ reducedForms D :=
  filter_subset _ _

namespace BinaryQuadraticForm

variable {D : ℕ} [NeZero D]

/-- A primitive reduced form of discriminant `-D` is a primitive positive definite form. -/
theorem mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ primitiveReducedForms D) : f ∈ posDef D ⊓ primitiveForms (-D) := by
  have hpos := mem_posDef.1 <|
    mem_posDef_of_mem_reducedForms (primitiveReducedForms_subset_reducedForms D hf)
  exact (mem_posDef_inf_primitiveForms D).2
    ⟨hpos.1, hpos.2, ((mem_primitiveReducedForms (NeZero.ne D)).1 hf).2.2⟩

/-- **The primitive reduced forms of discriminant `-D` represent the proper classes of primitive
positive definite forms**: sending a primitive reduced form to its proper equivalence class is a
bijection from `primitiveReducedForms D` onto `PosDefProperClass D` (Cohen, §5.3). -/
theorem posDefProperClass_mk_primitiveReducedForms_bijective :
    Function.Bijective fun f : primitiveReducedForms D ↦
      (Quotient.mk'' ⟨f, mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2⟩ :
        PosDefProperClass D) := by
  have hr (f : primitiveReducedForms D) : IsReducedForm f.1 :=
    ((mem_primitiveReducedForms (NeZero.ne D)).1 f.2).2.1
  have hpos (f : primitiveReducedForms D) : f.1 ∈ posDef D :=
    mem_posDef_of_mem_reducedForms (primitiveReducedForms_subset_reducedForms D f.2)
  refine ⟨fun f g h ↦ Subtype.ext ?_, Quotient.ind' fun f ↦ ?_⟩
  · -- proper equivalence of the primitive forms is proper equivalence of the positive definite
    -- forms, and the reduced representative of a positive definite class is unique
    obtain ⟨γ, hγ⟩ := Quotient.exact' h
    have hfg : (Quotient.mk'' ⟨f.1, hpos f⟩ : orbitRel.Quotient SL(2, ℤ) (posDef D)) =
        Quotient.mk'' ⟨g.1, hpos g⟩ :=
      Quotient.sound' ⟨γ, Subtype.ext <| by
        simpa only [SubMulAction.val_smul] using congrArg Subtype.val hγ⟩
    exact Subtype.mk.inj (orbit_mk_injOn_isReducedForm (by exact hr f) (by exact hr g) hfg)
  · -- reduce the form as a positive definite form; primitivity survives the change of variables
    have hf := (mem_posDef_inf_primitiveForms D).1 f.2
    obtain ⟨γ, hγ⟩ := exists_smul_isReducedForm (⟨f, mem_posDef.2 ⟨hf.1, hf.2.1⟩⟩ : posDef D)
    have hmem : γ • (f : BinaryQuadraticForm ℤ) ∈ primitiveReducedForms D :=
      (mem_primitiveReducedForms (NeZero.ne D)).2
        ⟨(discrim_smul γ _).trans hf.1, hγ, (isPrimitive_smul_iff _ γ).2 hf.2.2⟩
    exact ⟨⟨_, hmem⟩, Quotient.sound' ⟨γ, rfl⟩⟩

/-- There are finitely many proper classes of primitive positive definite forms of discriminant
`-D`. -/
instance finite_posDefProperClass : Finite (PosDefProperClass D) :=
  .of_surjective _ posDefProperClass_mk_primitiveReducedForms_bijective.2

/-- **The number of proper classes of primitive positive definite forms** of discriminant `-D` is
the number of primitive reduced forms of discriminant `-D`. -/
theorem nat_card_posDefProperClass : Nat.card (PosDefProperClass D) = #(primitiveReducedForms D) :=
  (Nat.card_eq_of_bijective _ posDefProperClass_mk_primitiveReducedForms_bijective).symm.trans
    (Nat.card_eq_finsetCard _)

/-! ### Imprimitive forms and the Hurwitz class number -/

/-- **Reduced forms split by their content**: a sum over the reduced forms of discriminant `-D` is
the sum, over the `g` with `g² ∣ D` and the primitive reduced forms `f` of discriminant `-D / g²`,
of the summand at `g • f`. Each reduced form is `g • f` for its content `g` and its primitive part
`f`, and for no other such pair. -/
theorem sum_reducedForms_eq_sum_sum_primitiveReducedForms {M : Type*} [AddCommMonoid M]
    {D : ℕ} (hD : D ≠ 0) (φ : BinaryQuadraticForm ℤ → M) :
    ∑ f ∈ reducedForms D, φ f = ∑ g ∈ D.divisors with g ^ 2 ∣ D,
      ∑ f ∈ primitiveReducedForms (D / g ^ 2), φ ((g : ℤ) • f) := by
  have hm {g : ℕ} (hg : g ^ 2 ∣ D) : D / g ^ 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hg)
      (Nat.pos_of_dvd_of_pos hg (Nat.pos_of_ne_zero hD))).ne'
  have hg0 {g : ℕ} (hg : g ∈ D.divisors) : g ≠ 0 := (Nat.pos_of_mem_divisors hg).ne'
  rw [sum_sigma', eq_comm]
  -- the bijection is `(g, f) ↦ g • f`, with inverse `f ↦ (content f, primPart f)`
  refine sum_nbij' (fun x ↦ (x.1 : ℤ) • x.2) (fun f ↦ ⟨f.content, f.primPart⟩) ?_ ?_ ?_ ?_
    fun _ _ ↦ rfl
  · rintro ⟨g, f⟩ h
    dsimp only at h ⊢
    obtain ⟨⟨hgD, hg⟩, hf⟩ := mem_sigma.1 h |>.imp_left mem_filter.1
    obtain ⟨hd, hr, -⟩ := (mem_primitiveReducedForms (hm hg)).1 hf
    rw [mem_reducedForms hD, discrim_natCast_smul_eq_neg_iff hg (hg0 hgD),
      isReducedForm_smul_iff (by have := hg0 hgD; positivity)]
    exact ⟨hd, hr⟩
  · intro f hf
    obtain ⟨hd, hr⟩ := (mem_reducedForms hD).1 hf
    have hf0 : f ≠ 0 := by rintro rfl; simp [discrim_def, discrim, hD] at hd
    have hc : 0 < f.content := f.content_pos_iff.2 hf0
    have hfp : (f.content : ℤ) • f.primPart = f := by rw [natCast_zsmul, content_smul_primPart]
    -- the square of the content divides the discriminant
    have hdvd : f.content ^ 2 ∣ D := by
      rw [← Int.natCast_dvd_natCast, ← dvd_neg, Nat.cast_pow, ← hd, discrim_eq_content_sq_mul]
      exact dvd_mul_right _ _
    refine mem_sigma.2 ⟨mem_filter.2 ⟨Nat.mem_divisors.2
      ⟨(Dvd.intro_left _ rfl).trans hdvd, hD⟩, hdvd⟩, ?_⟩
    rw [mem_primitiveReducedForms (hm hdvd), ← discrim_natCast_smul_eq_neg_iff hdvd hc.ne',
      ← isReducedForm_smul_iff (Int.natCast_pos.2 hc), hfp]
    exact ⟨hd, hr, f.isPrimitive_primPart hf0⟩
  · rintro ⟨g, f⟩ h
    dsimp only at h ⊢
    obtain ⟨⟨hgD, hg⟩, hf⟩ := mem_sigma.1 h |>.imp_left mem_filter.1
    obtain ⟨h₁, h₂⟩ := (eq_smul_iff_of_isPrimitive ((g : ℤ) • f) f
      (Nat.pos_of_ne_zero (hg0 hgD)) ((mem_primitiveReducedForms (hm hg)).1 hf).2.2).1 rfl
    rw [h₁, h₂]
  · intro f _
    rw [natCast_zsmul, content_smul_primPart]

/-- **Reduced forms counted by their content**: the number of reduced forms of discriminant `-D`
is the sum over the `g` with `g² ∣ D` of the number of primitive reduced forms of discriminant
`-D / g²`. -/
theorem card_reducedForms {D : ℕ} (hD : D ≠ 0) :
    #(reducedForms D) = ∑ g ∈ D.divisors with g ^ 2 ∣ D, #(primitiveReducedForms (D / g ^ 2)) := by
  simp only [card_eq_sum_ones]
  exact sum_reducedForms_eq_sum_sum_primitiveReducedForms hD fun _ ↦ 1

/-- A primitive form of discriminant neither `-3` nor `-4` has weight `1`: the only primitive forms
of another weight are `±(x² + y²)` and `±(x² + x y + y²)`. -/
theorem reducedFormWeight_eq_one_of_isPrimitive {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive)
    (h₃ : f.discrim ≠ -3) (h₄ : f.discrim ≠ -4) : reducedFormWeight f = 1 := by
  obtain ⟨a, b, c⟩ := f
  rw [isPrimitive_iff, content_def] at hf
  -- a primitive form `⟨a, 0, a⟩` or `⟨a, a, a⟩` has `a = ±1`
  refine reducedFormWeight_eq_one ?_ ?_ <;> dsimp only <;> rintro ⟨rfl, rfl⟩
  all_goals
    have ha : a.natAbs = 1 := by simpa [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_abs] using hf
    rcases Int.natAbs_eq_iff.1 ha with rfl | rfl <;>
      simp [discrim_def, discrim] at h₃ h₄

/-- **The weighted count of the primitive reduced forms** of discriminant `-n` is `2 h / w`, where
`h` is their number and `w` is `6` for `n = 3`, `4` for `n = 4` and `2` otherwise: every primitive
reduced form has weight `1` except `x² + x y + y²` and `x² + y²`, the only primitive reduced forms
of discriminant `-3` and `-4`. For `n ≡ 0, 3 (mod 4)`, `w` is the number of units of the quadratic
order of discriminant `-n` (`TauCeti.QuadraticOrder.card_units_of_neg`). -/
theorem sum_reducedFormWeight_primitiveReducedForms (n : ℕ) :
    ∑ f ∈ primitiveReducedForms n, reducedFormWeight f =
      2 * #(primitiveReducedForms n) / (if n = 3 then 6 else if n = 4 then 4 else 2 : ℚ) := by
  by_cases h₃ : n = 3
  · subst h₃
    decide +kernel
  by_cases h₄ : n = 4
  · subst h₄
    decide +kernel
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primitiveReducedForms]
  simp only [h₃, h₄, ↓reduceIte]
  rw [mul_div_cancel_left₀ _ two_ne_zero, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_congr rfl fun f hf ↦ ?_
  obtain ⟨hd, -, hp⟩ := (mem_primitiveReducedForms hn).1 hf
  exact reducedFormWeight_eq_one_of_isPrimitive hp (by lia) (by lia)

end BinaryQuadraticForm

open BinaryQuadraticForm

/-- **The Hurwitz class number from the primitive class numbers**: for `D ≠ 0`,
```
H(D) = ∑_{g² ∣ D} 2 h(D / g²) / w(D / g²),
```
where `h(n)` is the number of primitive reduced forms of discriminant `-n`, that is of proper
classes of primitive positive definite forms (`nat_card_posDefProperClass`), and `w(n)` is `6` for
`n = 3`, `4` for `n = 4` and `2` otherwise. The imprimitive forms `g • f` contribute through the
terms with `g > 1`, and the exceptional weights `1/3` and `1/2` through `w`. -/
theorem hurwitzClassNumber_eq_sum_card_primitiveReducedForms {D : ℕ} (hD : D ≠ 0) :
    hurwitzClassNumber D = ∑ g ∈ D.divisors with g ^ 2 ∣ D,
      2 * #(primitiveReducedForms (D / g ^ 2)) /
        (if D / g ^ 2 = 3 then 6 else if D / g ^ 2 = 4 then 4 else 2 : ℚ) := by
  rw [hurwitzClassNumber_of_ne_zero hD, sum_reducedForms_eq_sum_sum_primitiveReducedForms hD]
  refine sum_congr rfl fun g hg ↦ ?_
  have hg0 : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (Nat.pos_of_mem_divisors (mem_filter.1 hg).1).ne'
  simp only [reducedFormWeight_smul hg0, sum_reducedFormWeight_primitiveReducedForms]

end TauCeti
