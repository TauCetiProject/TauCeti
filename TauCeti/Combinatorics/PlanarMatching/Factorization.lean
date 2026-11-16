/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.ArcInsertion
public import TauCeti.Combinatorics.PlanarMatching.Associativity
public import TauCeti.Combinatorics.PlanarMatching.HalfDiagram.Glue

/-!
# Through-strand factorization of Temperley–Lieb diagrams

Every Temperley–Lieb diagram `D : n → m` cuts horizontally into its bottom half-diagram
`D.bottomHalf : HalfDiagram n D.through` and its top half-diagram
`D.topHalf : HalfDiagram m D.through`, glued across `D.through` defects. This file upgrades that
combinatorial cut-and-glue decomposition into the categorical **through-strand factorization** of
diagrams under composition (`TauCeti.TLDiagram.comp`):

1. A diagram `D : n → m` is **string-injective** (`TauCeti.TLDiagram.StringInjective`) if
   `D.through = n` (all bottom boundary points lie on through strands, i.e. no bottom caps), and
   **string-surjective** (`TauCeti.TLDiagram.StringSurjective`) if `D.through = m` (all top
   boundary points lie on through strands, i.e. no top cups).
2. Post-composing any diagram with a string-injective diagram adds their circle counts and
   preserves both the through-strand count and the bottom half-diagram
   (`TauCeti.TLDiagram.circles_comp_of_stringInjective`,
   `TauCeti.TLDiagram.through_comp_of_stringInjective`,
   `TauCeti.TLDiagram.bottomHalf_comp_val_of_stringInjective`); dual statements for pre-composing
   with a string-surjective diagram follow by vertical reflection.
3. Every diagram `D : n → m` factors through `D.through` as `D.surjection.comp D.injection = D`
   (`TauCeti.TLDiagram.surjection_comp_injection`), where `D.surjection` is string-surjective and
   carries `D.circles`, while `D.injection` is string-injective and circle-free. This factorization
   is unique (`TauCeti.TLDiagram.existsUnique_factorization`).
4. **Re-factorization** (`TauCeti.TLDiagram.refactorization`) computes the canonical factorization
   of `(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` by re-factoring the middle composite `i₁ ≫ s₂`, yielding monotonic
   filtration bounds `(f ≫ g).through ≤ min f.through g.through` and the cellular multiplication
   formula (`TauCeti.TLDiagram.glue_comp_glue_of_through_eq`).
5. **Cancellation and invertibility**: a diagram is right-cancellative (monic) if and only if it is
   string-injective (`TauCeti.TLDiagram.stringInjective_iff_comp_left_injective`),
   left-cancellative (epic) if and only if it is string-surjective
   (`TauCeti.TLDiagram.stringSurjective_iff_comp_right_injective`), two-sided inverse diagrams force
   equal boundary counts (`TauCeti.TLDiagram.eq_of_comp_eq_id`), and the only right-invertible
   endomorphism diagram is the identity (`TauCeti.TLDiagram.eq_id_of_comp_eq_id`).

## Main definitions

* `TauCeti.TLDiagram.StringInjective`, `TauCeti.TLDiagram.StringSurjective`: diagrams whose bottom
  (resp. top) points all lie on through strands.
* `TauCeti.HalfDiagram.toSurjection`, `TauCeti.HalfDiagram.toInjection`: circle-free string
  surjections and injections built by gluing a half-diagram to `HalfDiagram.id k`.
* `TauCeti.TLDiagram.surjection`, `TauCeti.TLDiagram.injection`: the canonical surjective and
  injective factors of a diagram `D` through `D.through`.

## Main results

* `TauCeti.TLDiagram.StringInjective.induction`, `TauCeti.TLDiagram.StringSurjective.induction`:
  structural cup- and cap-peeling induction principles.
* `TauCeti.TLDiagram.surjection_comp_injection`, `TauCeti.TLDiagram.existsUnique_factorization`:
  existence and uniqueness of through-strand factorization.
* `TauCeti.TLDiagram.refactorization`, `TauCeti.TLDiagram.through_comp_eq`,
  `TauCeti.TLDiagram.circles_comp_eq`, `TauCeti.TLDiagram.glue_comp_glue_of_through_eq`:
  re-factorization, filtration of through strands, and cellular multiplication.
* `TauCeti.TLDiagram.stringInjective_iff_comp_left_injective`,
  `TauCeti.TLDiagram.stringSurjective_iff_comp_right_injective`: combinatorial characterization of
  cancellative diagrams.
* `TauCeti.TLDiagram.eq_of_comp_eq_id`, `TauCeti.TLDiagram.eq_id_of_comp_eq_id`: two-sided
  inverses force equal boundary counts, and the only right-invertible endomorphism diagram is the
  identity.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. **123** (1996), 1–34.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

open Equiv

namespace TauCeti

/-! ### String-injective and string-surjective diagrams -/

namespace TLDiagram

variable {n m p q k k₁ k₂ : ℕ}

/-- A Temperley–Lieb diagram `D : n → m` is **string-injective** if all `n` bottom boundary points
lie on through strands (`D.through = n`), equivalently its bottom half-diagram has no caps. -/
def StringInjective (D : TLDiagram n m) : Prop := D.through = n

/-- A Temperley–Lieb diagram `D : n → m` is **string-surjective** if all `m` top boundary points
lie on through strands (`D.through = m`), equivalently its top half-diagram has no cups. -/
def StringSurjective (D : TLDiagram n m) : Prop := D.through = m

theorem stringInjective_iff {D : TLDiagram n m} : D.StringInjective ↔ D.through = n := Iff.rfl
theorem stringSurjective_iff {D : TLDiagram n m} : D.StringSurjective ↔ D.through = m := Iff.rfl

instance (D : TLDiagram n m) : Decidable D.StringInjective :=
  inferInstanceAs (Decidable (D.through = n))

instance (D : TLDiagram n m) : Decidable D.StringSurjective :=
  inferInstanceAs (Decidable (D.through = m))

theorem StringInjective.through_eq {D : TLDiagram n m} (h : D.StringInjective) : D.through = n := h
theorem StringSurjective.through_eq {D : TLDiagram n m} (h : D.StringSurjective) :
    D.through = m := h

theorem StringInjective.le {D : TLDiagram n m} (h : D.StringInjective) : n ≤ m :=
  h ▸ D.through_le_top

theorem StringSurjective.le {D : TLDiagram n m} (h : D.StringSurjective) : m ≤ n :=
  h ▸ D.through_le_bottom

theorem StringInjective.even_sub {D : TLDiagram n m} (h : D.StringInjective) : Even (m - n) :=
  h ▸ D.even_top_sub_through

theorem StringSurjective.even_sub {D : TLDiagram n m} (h : D.StringSurjective) : Even (n - m) :=
  h ▸ D.even_bottom_sub_through

/-- A diagram is string-injective precisely when its bottom half-diagram has no arcs. -/
theorem stringInjective_iff_bottomHalf_val_eq_one {D : TLDiagram n m} :
    D.StringInjective ↔ D.bottomHalf.val = 1 := HalfDiagram.val_eq_one_iff.symm

/-- A diagram is string-surjective precisely when its top half-diagram has no arcs. -/
theorem stringSurjective_iff_topHalf_val_eq_one {D : TLDiagram n m} :
    D.StringSurjective ↔ D.topHalf.val = 1 := HalfDiagram.val_eq_one_iff.symm

@[simp] theorem stringSurjective_verticalReflect_iff {D : TLDiagram n m} :
    (verticalReflect n m D).StringSurjective ↔ D.StringInjective := by
  simp [StringSurjective, StringInjective]

@[simp] theorem stringInjective_verticalReflect_iff {D : TLDiagram n m} :
    (verticalReflect n m D).StringInjective ↔ D.StringSurjective := by
  simp [StringSurjective, StringInjective]

theorem StringInjective.verticalReflect {D : TLDiagram n m} (h : D.StringInjective) :
    (TLDiagram.verticalReflect n m D).StringSurjective :=
  stringSurjective_verticalReflect_iff.mpr h

theorem StringSurjective.verticalReflect {D : TLDiagram n m} (h : D.StringSurjective) :
    (TLDiagram.verticalReflect n m D).StringInjective :=
  stringInjective_verticalReflect_iff.mpr h

@[simp] theorem stringInjective_id (n : ℕ) : (id n).StringInjective := through_id n
@[simp] theorem stringSurjective_id (n : ℕ) : (id n).StringSurjective := through_id n

/-- Every diagram with empty bottom boundary is string-injective. -/
@[simp] theorem stringInjective_zero_left (D : TLDiagram 0 m) : D.StringInjective :=
  through_zero_left D

/-- Every diagram with empty top boundary is string-surjective. -/
@[simp] theorem stringSurjective_zero_right (D : TLDiagram n 0) : D.StringSurjective :=
  through_zero_right D

@[simp] theorem stringInjective_cupAt (c : Fin (q + 1)) : (cupAt c).StringInjective :=
  through_cupAt c
@[simp] theorem stringSurjective_capAt (c : Fin (q + 1)) : (capAt c).StringSurjective :=
  through_capAt c

private theorem verticalReflect_mk_nested (n c : ℕ) :
    verticalReflect n n ⟨PlanarMatching.nested n, c⟩ = ⟨PlanarMatching.nested n, c⟩ := by
  have hth : (verticalReflect n n ⟨PlanarMatching.nested n, c⟩).through = n := by
    rw [through_verticalReflect, through_eq_of_matching_eq (E := id n) (matching_id n).symm,
      through_id]
  simpa only [circles_verticalReflect] using eq_mk_nested_of_through_eq hth

/-- **Structural induction on string-injective diagrams**: every string-injective diagram `n → m`
is obtained from `⟨PlanarMatching.nested n, c⟩` by post-composing finitely many elementary cups
`cupAt`. -/
@[elab_as_elim]
theorem StringInjective.induction {n : ℕ}
    {P : ∀ {m : ℕ} (D : TLDiagram n m), D.StringInjective → Prop}
    (base : ∀ c : ℕ, P ⟨PlanarMatching.nested n, c⟩
      (by rw [stringInjective_iff, through_eq_of_matching_eq (E := id n) (matching_id n).symm,
            through_id]))
    (step : ∀ {q : ℕ} (D : TLDiagram n q) (hD : D.StringInjective) (c : Fin (q + 1)),
      P D hD → P (D.comp (cupAt c))
        (by rw [comp_cupAt, stringInjective_iff, through_insertTopArc]; exact hD))
    {m : ℕ} {D : TLDiagram n m} (hD : D.StringInjective) : P D hD := by
  suffices ∀ (d : ℕ) {m : ℕ} (D : TLDiagram n m) (hD : D.StringInjective),
      m - n = 2 * d → P D hD from
    this ((m - n) / 2) D hD (by have := Nat.even_iff.mp hD.even_sub; omega)
  intro d; induction d with
  | zero =>
    intro m D hD hd
    obtain rfl : n = m := le_antisymm hD.le (by omega)
    convert base D.circles using 1
    exact eq_mk_nested_of_through_eq hD
  | succ d ih =>
    intro m D hD hd
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by have := hD.le; omega⟩
    obtain ⟨c, hc⟩ := D.topHalf.exists_apply_castSucc_eq_succ (by rw [hD.through_eq]; omega)
    obtain ⟨D', hth', -, hD_eq⟩ := exists_comp_cupAt_of_topHalf_apply_eq hc
    have hD' : D'.StringInjective := hth'.trans hD
    convert step D' hD' c (ih D' hD' (by have := hD'.le; omega)) using 1
    exact hD_eq.symm

/-- **Structural induction on string-surjective diagrams**: every string-surjective diagram
`n → m` is obtained from `⟨PlanarMatching.nested m, c⟩` by pre-composing finitely many elementary
caps `capAt`. -/
@[elab_as_elim]
theorem StringSurjective.induction {m : ℕ}
    {P : ∀ {n : ℕ} (D : TLDiagram n m), D.StringSurjective → Prop}
    (base : ∀ c : ℕ, P ⟨PlanarMatching.nested m, c⟩
      (by rw [stringSurjective_iff, through_eq_of_matching_eq (E := id m) (matching_id m).symm,
            through_id]))
    (step : ∀ {q : ℕ} (D : TLDiagram q m) (hD : D.StringSurjective) (c : Fin (q + 1)),
      P D hD → P ((capAt c).comp D)
        (by rw [capAt_comp, stringSurjective_iff, through_insertBottomArc]; exact hD))
    {n : ℕ} {D : TLDiagram n m} (hD : D.StringSurjective) : P D hD := by
  have h : ∀ {n : ℕ} (E : TLDiagram m n) (hE : E.StringInjective),
      P (TLDiagram.verticalReflect m n E) hE.verticalReflect := by
    intro n E hE
    induction hE using StringInjective.induction with
    | base c =>
      have hv := verticalReflect_mk_nested m c
      convert base c using 1
    | step E' hE' c ih =>
      have hv : TLDiagram.verticalReflect m _ (E'.comp (cupAt c)) =
          (capAt c).comp (TLDiagram.verticalReflect m _ E') := by
        rw [verticalReflect_comp, verticalReflect_cupAt]
      convert step (TLDiagram.verticalReflect m _ E') hE'.verticalReflect c ih using 1
  have hD' := h (TLDiagram.verticalReflect n m D) hD.verticalReflect
  simpa only [verticalReflect_verticalReflect] using hD'

end TLDiagram

/-! ### Embedding half-diagrams and canonical through-strand factors -/

namespace HalfDiagram

variable {n m k : ℕ}

/-- View a half-diagram `B : HalfDiagram n k` as a circle-free string-surjective diagram `n → k`
by joining its `k` defects in order to the `k` top boundary points. -/
def toSurjection (B : HalfDiagram n k) : TLDiagram n k := ⟨B.glue (HalfDiagram.id k), 0⟩

/-- View a half-diagram `T : HalfDiagram m k` as a circle-free string-injective diagram `k → m`
by joining the `k` bottom boundary points in order to the `k` defects of `T` on the top. -/
def toInjection (T : HalfDiagram m k) : TLDiagram k m := ⟨(HalfDiagram.id k).glue T, 0⟩

@[simp] theorem matching_toSurjection (B : HalfDiagram n k) :
    B.toSurjection.matching = B.glue (HalfDiagram.id k) := (rfl)
@[simp] theorem circles_toSurjection (B : HalfDiagram n k) : B.toSurjection.circles = 0 := (rfl)
@[simp] theorem through_toSurjection (B : HalfDiagram n k) : B.toSurjection.through = k :=
  B.through_glue (HalfDiagram.id k)
@[simp] theorem bottomHalf_toSurjection_val (B : HalfDiagram n k) :
    B.toSurjection.bottomHalf.val = B.val := B.bottomHalf_glue_val (HalfDiagram.id k)
@[simp] theorem topHalf_toSurjection_val (B : HalfDiagram n k) : B.toSurjection.topHalf.val = 1 :=
  (B.topHalf_glue_val (HalfDiagram.id k)).trans (HalfDiagram.id_val k)
@[simp] theorem stringSurjective_toSurjection (B : HalfDiagram n k) :
    B.toSurjection.StringSurjective := B.through_toSurjection

@[simp] theorem matching_toInjection (T : HalfDiagram m k) :
    T.toInjection.matching = (HalfDiagram.id k).glue T := (rfl)
@[simp] theorem circles_toInjection (T : HalfDiagram m k) : T.toInjection.circles = 0 := (rfl)
@[simp] theorem through_toInjection (T : HalfDiagram m k) : T.toInjection.through = k :=
  (HalfDiagram.id k).through_glue T
@[simp] theorem bottomHalf_toInjection_val (T : HalfDiagram m k) :
    T.toInjection.bottomHalf.val = 1 :=
  ((HalfDiagram.id k).bottomHalf_glue_val T).trans (HalfDiagram.id_val k)
@[simp] theorem topHalf_toInjection_val (T : HalfDiagram m k) :
    T.toInjection.topHalf.val = T.val := (HalfDiagram.id k).topHalf_glue_val T
@[simp] theorem stringInjective_toInjection (T : HalfDiagram m k) :
    T.toInjection.StringInjective := T.through_toInjection

@[simp] theorem toSurjection_id (k : ℕ) : (HalfDiagram.id k).toSurjection = TLDiagram.id k :=
  TLDiagram.ext_halves (by simp) (by simp) (by simp)
@[simp] theorem toInjection_id (k : ℕ) : (HalfDiagram.id k).toInjection = TLDiagram.id k :=
  TLDiagram.ext_halves (by simp) (by simp) (by simp)
@[simp] theorem verticalReflect_toSurjection (B : HalfDiagram n k) :
    TLDiagram.verticalReflect n k B.toSurjection = B.toInjection :=
  TLDiagram.ext_halves (by rw [← TLDiagram.topHalf_val]; simp) (by simp) (by simp)
@[simp] theorem verticalReflect_toInjection (T : HalfDiagram m k) :
    TLDiagram.verticalReflect k m T.toInjection = T.toSurjection := by
  rw [← verticalReflect_toSurjection, TLDiagram.verticalReflect_verticalReflect]

theorem toSurjection_injective : Function.Injective (@toSurjection n k) :=
  fun _ _ h => Subtype.ext <| by
    simpa using TLDiagram.bottomHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching h)

theorem toInjection_injective : Function.Injective (@toInjection m k) :=
  fun _ _ h => Subtype.ext <| by
    simpa using TLDiagram.topHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching h)

/-- A diagram lies in the image of `HalfDiagram.toSurjection` precisely when it is
string-surjective and carries no closed circles. -/
theorem exists_toSurjection_eq_iff {D : TLDiagram n k} :
    (∃ B : HalfDiagram n k, B.toSurjection = D) ↔ D.StringSurjective ∧ D.circles = 0 := by
  refine ⟨?_, fun ⟨hs, hc⟩ => ?_⟩
  · rintro ⟨B, rfl⟩; exact ⟨B.stringSurjective_toSurjection, B.circles_toSurjection⟩
  · refine ⟨⟨D.bottomHalf.val, D.bottomHalf.2.1, D.bottomHalf.2.2.trans hs⟩,
      TLDiagram.ext_halves (by simp)
        (by simp [TLDiagram.stringSurjective_iff_topHalf_val_eq_one.mp hs]) hc.symm⟩

/-- A diagram lies in the image of `HalfDiagram.toInjection` precisely when it is
string-injective and carries no closed circles. -/
theorem exists_toInjection_eq_iff {D : TLDiagram k m} :
    (∃ T : HalfDiagram m k, T.toInjection = D) ↔ D.StringInjective ∧ D.circles = 0 := by
  refine ⟨?_, fun ⟨hi, hc⟩ => ?_⟩
  · rintro ⟨T, rfl⟩; exact ⟨T.stringInjective_toInjection, T.circles_toInjection⟩
  · refine ⟨⟨D.topHalf.val, D.topHalf.2.1, D.topHalf.2.2.trans hi⟩,
      TLDiagram.ext_halves
        (by simp [TLDiagram.stringInjective_iff_bottomHalf_val_eq_one.mp hi])
        (by simp) hc.symm⟩

end HalfDiagram

namespace TLDiagram

variable {n m p q k k₁ k₂ : ℕ}

/-- The **surjective factor** of `D : n → m` in its canonical through-strand factorization: it
keeps the bottom caps and closed circles of `D`, and sends its `D.through` defects straight to the
intermediate boundary. -/
def surjection (D : TLDiagram n m) : TLDiagram n D.through :=
  ⟨D.bottomHalf.glue (HalfDiagram.id D.through), D.circles⟩

/-- The **injective factor** of `D : n → m` in its canonical through-strand factorization: it has
no closed circles, sends the `D.through` intermediate boundary points to the top defects of `D`,
and keeps the top cups of `D`. -/
def injection (D : TLDiagram n m) : TLDiagram D.through m := D.topHalf.toInjection

@[simp] theorem matching_surjection (D : TLDiagram n m) :
    D.surjection.matching = D.bottomHalf.glue (HalfDiagram.id D.through) := (rfl)
@[simp] theorem circles_surjection (D : TLDiagram n m) : D.surjection.circles = D.circles := (rfl)
@[simp] theorem through_surjection (D : TLDiagram n m) : D.surjection.through = D.through :=
  D.bottomHalf.through_glue (HalfDiagram.id D.through)
@[simp] theorem bottomHalf_surjection_val (D : TLDiagram n m) :
    D.surjection.bottomHalf.val = D.bottomHalf.val :=
  D.bottomHalf.bottomHalf_glue_val (HalfDiagram.id D.through)
@[simp] theorem topHalf_surjection_val (D : TLDiagram n m) : D.surjection.topHalf.val = 1 :=
  (D.bottomHalf.topHalf_glue_val (HalfDiagram.id D.through)).trans (HalfDiagram.id_val _)
@[simp] theorem stringSurjective_surjection (D : TLDiagram n m) : D.surjection.StringSurjective :=
  D.through_surjection

@[simp] theorem matching_injection (D : TLDiagram n m) :
    D.injection.matching = (HalfDiagram.id D.through).glue D.topHalf := (rfl)
@[simp] theorem circles_injection (D : TLDiagram n m) : D.injection.circles = 0 := (rfl)
@[simp] theorem through_injection (D : TLDiagram n m) : D.injection.through = D.through :=
  D.topHalf.through_toInjection
@[simp] theorem bottomHalf_injection_val (D : TLDiagram n m) : D.injection.bottomHalf.val = 1 :=
  D.topHalf.bottomHalf_toInjection_val
@[simp] theorem topHalf_injection_val (D : TLDiagram n m) :
    D.injection.topHalf.val = D.topHalf.val := D.topHalf.topHalf_toInjection_val
@[simp] theorem stringInjective_injection (D : TLDiagram n m) : D.injection.StringInjective :=
  D.through_injection

/-- The canonical injective factor of `D` is the injection associated with `D.topHalf`. -/
theorem injection_eq_topHalf_toInjection (D : TLDiagram n m) :
    D.injection = D.topHalf.toInjection := (rfl)

/-- The canonical surjective factor of `D` is `D.bottomHalf.toSurjection` carrying `D.circles`
closed circles. -/
theorem surjection_eq_toSurjection_comp_mk_nested (D : TLDiagram n m) :
    D.surjection = D.bottomHalf.toSurjection.comp ⟨PlanarMatching.nested D.through, D.circles⟩ := by
  rw [comp_mk_nested]; exact TLDiagram.ext rfl (by simp)

/-! ### Composition with string injections and surjections -/

private theorem comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) :
    (f.comp g).circles = f.circles + g.circles ∧
      (f.comp g).bottomHalf.val = f.bottomHalf.val := by
  induction hg using StringInjective.induction with
  | base c =>
    rw [comp_mk_nested]
    exact ⟨rfl, bottomHalf_val_eq_of_matching_eq rfl⟩
  | step g' _ c ih =>
    have hassoc : f.comp (g'.comp (cupAt c)) = (f.comp g').insertTopArc c := by
      rw [← comp_assoc, comp_cupAt]
    have hcirc' : (g'.comp (cupAt c)).circles = g'.circles := by
      rw [comp_cupAt, circles_insertTopArc]
    exact ⟨by rw [hassoc, circles_insertTopArc, ih.1, hcirc'],
      by rw [bottomHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching hassoc),
           bottomHalf_insertTopArc_val, ih.2]⟩

/-- Post-composing with a string-injective diagram closes no new circles in the middle: the total
circle count is simply `f.circles + g.circles`. -/
theorem circles_comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).circles = f.circles + g.circles :=
  (comp_of_stringInjective f hg).1

/-- Post-composing with a string-injective diagram preserves the bottom half-diagram. -/
theorem bottomHalf_comp_val_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).bottomHalf.val = f.bottomHalf.val :=
  (comp_of_stringInjective f hg).2

/-- Post-composing with a string-injective diagram preserves the number of through strands. -/
theorem through_comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).through = f.through :=
  through_eq_of_bottomHalf_val_eq (bottomHalf_comp_val_of_stringInjective f hg)

/-- Pre-composing with a string-surjective diagram closes no new circles in the middle. -/
theorem circles_comp_of_stringSurjective {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).circles = f.circles + g.circles := by
  rw [← circles_verticalReflect (f.comp g), verticalReflect_comp,
    circles_comp_of_stringInjective _ hf.verticalReflect, circles_verticalReflect,
    circles_verticalReflect, add_comm]

/-- Pre-composing with a string-surjective diagram preserves the top half-diagram. -/
theorem topHalf_comp_val_of_stringSurjective {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).topHalf.val = g.topHalf.val := by
  rw [topHalf_val,
    bottomHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching (verticalReflect_comp f g)),
    bottomHalf_comp_val_of_stringInjective _ hf.verticalReflect, ← topHalf_val]

/-- Pre-composing with a string-surjective diagram preserves the number of through strands. -/
theorem through_comp_of_stringSurjective {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).through = g.through :=
  through_eq_of_topHalf_val_eq (topHalf_comp_val_of_stringSurjective g hf)

/-- String-injective diagrams are closed under composition. -/
theorem StringInjective.comp {f : TLDiagram n m} {g : TLDiagram m p}
    (hf : f.StringInjective) (hg : g.StringInjective) : (f.comp g).StringInjective := by
  rw [StringInjective, through_comp_of_stringInjective f hg, hf.through_eq]

/-- String-surjective diagrams are closed under composition. -/
theorem StringSurjective.comp {f : TLDiagram n m} {g : TLDiagram m p}
    (hf : f.StringSurjective) (hg : g.StringSurjective) : (f.comp g).StringSurjective := by
  rw [StringSurjective, through_comp_of_stringSurjective g hf, hg.through_eq]

/-! ### Existence and uniqueness of through-strand factorization -/

/-- Composing the canonical surjection of `B` with the canonical injection of `T` glues `B` and `T`
with no closed circles. -/
@[simp]
theorem _root_.TauCeti.HalfDiagram.toSurjection_comp_toInjection (B : HalfDiagram n k)
    (T : HalfDiagram m k) : B.toSurjection.comp T.toInjection = ⟨B.glue T, 0⟩ :=
  ext_halves
    (by rw [bottomHalf_comp_val_of_stringInjective _ T.stringInjective_toInjection]; simp)
    (by rw [topHalf_comp_val_of_stringSurjective _ B.stringSurjective_toSurjection]; simp)
    (by rw [circles_comp_of_stringInjective _ T.stringInjective_toInjection]; simp)

/-- **Through-strand factorization**: every Temperley–Lieb diagram `D : n → m` is the composite of
its canonical surjective factor `D.surjection : n → D.through` followed by its canonical injective
factor `D.injection : D.through → m`. -/
@[simp]
theorem surjection_comp_injection (D : TLDiagram n m) : D.surjection.comp D.injection = D :=
  ext_halves
    (by rw [bottomHalf_comp_val_of_stringInjective _ D.stringInjective_injection]; simp)
    (by rw [topHalf_comp_val_of_stringSurjective _ D.stringSurjective_surjection]; simp)
    (by rw [circles_comp_of_stringInjective _ D.stringInjective_injection]; simp)

/-- Composing a string-surjective diagram `n → k` with a string-injective diagram `k → m` produces
a diagram with exactly `k` through strands. -/
theorem through_comp_of_stringSurjective_of_stringInjective {s : TLDiagram n k}
    {i : TLDiagram k m} (hs : s.StringSurjective) (hi : i.StringInjective) :
    (s.comp i).through = k := by
  rw [through_comp_of_stringInjective s hi, hs.through_eq]

/-- In any factorization `s.comp i = D` into a string-surjective `s : n → k` and a string-injective
`i : k → m`, the through-strand count `D.through` must equal `k`. -/
theorem through_eq_of_comp_eq {D : TLDiagram n m} {s : TLDiagram n k} {i : TLDiagram k m}
    (hs : s.StringSurjective) (hi : i.StringInjective) (h : s.comp i = D) :
    D.through = k := by
  rw [← h, through_comp_of_stringSurjective_of_stringInjective hs hi]

/-- Associativity and factorization rewrite `(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` by re-factoring the middle
composite `i₁ ≫ s₂`. -/
theorem comp_eq_refactorization (s₁ : TLDiagram n k₁) (i₁ : TLDiagram k₁ m)
    (s₂ : TLDiagram m k₂) (i₂ : TLDiagram k₂ p) :
    (s₁.comp i₁).comp (s₂.comp i₂) =
      (s₁.comp (i₁.comp s₂).surjection).comp ((i₁.comp s₂).injection.comp i₂) := by
  symm; rw [comp_assoc, ← comp_assoc (i₁.comp s₂).surjection, surjection_comp_injection,
    comp_assoc, comp_assoc]

/-- Under `s₁.StringSurjective` and `i₂.StringInjective`, the through-strand count of
`(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` is that of the middle composite `i₁ ≫ s₂`. -/
theorem through_comp_comp_of_stringSurjective_of_stringInjective {s₁ : TLDiagram n k₁}
    (i₁ : TLDiagram k₁ m) (s₂ : TLDiagram m k₂) {i₂ : TLDiagram k₂ p}
    (hs₁ : s₁.StringSurjective) (hi₂ : i₂.StringInjective) :
    ((s₁.comp i₁).comp (s₂.comp i₂)).through = (i₁.comp s₂).through := by
  rw [comp_eq_refactorization, through_comp_of_stringSurjective_of_stringInjective
    (hs₁.comp (stringSurjective_surjection _)) ((stringInjective_injection _).comp hi₂)]

/-- The through-strand count of `f ≫ g` equals that of the middle pairing
`f.injection ≫ g.surjection : f.through → g.through`. -/
theorem through_comp_eq (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).through = (f.injection.comp g.surjection).through := by
  conv_lhs => rw [← f.surjection_comp_injection, ← g.surjection_comp_injection]
  exact through_comp_comp_of_stringSurjective_of_stringInjective _ _
    f.stringSurjective_surjection g.stringInjective_injection

/-- Composition cannot increase the number of through strands beyond that of the bottom factor. -/
theorem through_comp_le_left (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).through ≤ f.through :=
  (through_comp_eq f g).trans_le (f.injection.comp g.surjection).through_le_bottom

/-- Composition cannot increase the number of through strands beyond that of the top factor. -/
theorem through_comp_le_right (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).through ≤ g.through :=
  (through_comp_eq f g).trans_le (f.injection.comp g.surjection).through_le_top

/-- **Through-strand filtration**: `(f ≫ g).through ≤ min f.through g.through`. -/
theorem through_comp_le_min (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).through ≤ min f.through g.through :=
  le_min (through_comp_le_left f g) (through_comp_le_right f g)

/-- **Uniqueness of through-strand factors** at `D.through` once closed circles are pinned to the
left factor (`i.circles = 0`). String-surjectivity of `s` and string-injectivity of `i` are forced
automatically by `(s ≫ i).through ≤ min s.through i.through`. -/
theorem eq_surjection_and_eq_injection_of_comp_eq {D : TLDiagram n m}
    {s : TLDiagram n D.through} {i : TLDiagram D.through m} (hc : i.circles = 0)
    (h : s.comp i = D) : s = D.surjection ∧ i = D.injection := by
  have hs : s.StringSurjective := le_antisymm s.through_le_top
    ((congrArg TLDiagram.through h).symm.trans_le (through_comp_le_left s i))
  have hi : i.StringInjective := le_antisymm i.through_le_bottom
    ((congrArg TLDiagram.through h).symm.trans_le (through_comp_le_right s i))
  have hcirc := congrArg TLDiagram.circles h
  rw [circles_comp_of_stringInjective s hi, hc, add_zero] at hcirc
  exact ⟨ext_halves (by rw [← bottomHalf_comp_val_of_stringInjective s hi,
      bottomHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching h), bottomHalf_surjection_val])
    (by rw [stringSurjective_iff_topHalf_val_eq_one.mp hs, topHalf_surjection_val])
    (hcirc.trans D.circles_surjection.symm),
    ext_halves (by rw [stringInjective_iff_bottomHalf_val_eq_one.mp hi, bottomHalf_injection_val])
    (by rw [← topHalf_comp_val_of_stringSurjective i hs,
      topHalf_val_eq_of_matching_eq (congrArg TLDiagram.matching h),
      topHalf_injection_val]) (hc.trans D.circles_injection.symm)⟩

/-- **Existence and uniqueness of through-strand factorization.** Every diagram `D : n → m`
factors through a unique intermediate strand count `k` as a string-surjective diagram `s : n → k`
followed by a circle-free string-injective diagram `i : k → m`, namely `k = D.through`,
`s = D.surjection`, and `i = D.injection`. -/
theorem existsUnique_factorization (D : TLDiagram n m) :
    ∃! p : Σ k : ℕ, TLDiagram n k × TLDiagram k m,
      p.2.1.StringSurjective ∧ p.2.2.StringInjective ∧ p.2.2.circles = 0 ∧
        p.2.1.comp p.2.2 = D := by
  refine ⟨⟨D.through, D.surjection, D.injection⟩, ⟨D.stringSurjective_surjection,
    D.stringInjective_injection, D.circles_injection, D.surjection_comp_injection⟩, ?_⟩
  rintro ⟨k, s, i⟩ ⟨hs, hi, hc, hcomp⟩
  obtain rfl : D.through = k := through_eq_of_comp_eq hs hi hcomp
  obtain ⟨rfl, rfl⟩ := eq_surjection_and_eq_injection_of_comp_eq hc hcomp; rfl

/-! ### Re-factorization and cellular multiplication -/

/-- **Re-factorization of a composite from factored inputs.** Given `s₁ : n → k₁` string-surjective,
arbitrary middle diagrams `i₁ : k₁ → m` and `s₂ : m → k₂`, and a circle-free string-injective
`i₂ : k₂ → p`, the canonical through-strand factorization of `(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` has
intermediate strand count `(i₁ ≫ s₂).through`, surjective factor `s₁ ≫ (i₁ ≫ s₂).surjection`, and
injective factor `(i₁ ≫ s₂).injection ≫ i₂`. -/
theorem refactorization {s₁ : TLDiagram n k₁} (i₁ : TLDiagram k₁ m)
    (s₂ : TLDiagram m k₂) {i₂ : TLDiagram k₂ p}
    (hs₁ : s₁.StringSurjective) (hi₂ : i₂.StringInjective) (hc₂ : i₂.circles = 0) :
    (⟨(i₁.comp s₂).through,
        s₁.comp (i₁.comp s₂).surjection, (i₁.comp s₂).injection.comp i₂⟩ :
      Σ k : ℕ, TLDiagram n k × TLDiagram k p) =
      ⟨((s₁.comp i₁).comp (s₂.comp i₂)).through,
        ((s₁.comp i₁).comp (s₂.comp i₂)).surjection,
        ((s₁.comp i₁).comp (s₂.comp i₂)).injection⟩ := by
  let D := (s₁.comp i₁).comp (s₂.comp i₂)
  refine (existsUnique_factorization D).unique
    ⟨hs₁.comp (stringSurjective_surjection _), (stringInjective_injection _).comp hi₂, ?_,
      (comp_eq_refactorization s₁ i₁ s₂ i₂).symm⟩
    ⟨D.stringSurjective_surjection, D.stringInjective_injection, D.circles_injection,
      D.surjection_comp_injection⟩
  rw [circles_comp_of_stringInjective _ hi₂, circles_injection, hc₂, add_zero]

/-- The circles closed in the middle of `f ≫ g` depend only on the pairing of `f.topHalf` against
`g.bottomHalf`. -/
theorem circles_comp_eq (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).circles = f.circles + g.circles +
      (f.topHalf.toInjection.comp g.bottomHalf.toSurjection).circles := by
  have hmid : ((f.bottomHalf.toSurjection.comp f.topHalf.toInjection).comp
      (g.bottomHalf.toSurjection.comp g.topHalf.toInjection)).circles =
      (f.topHalf.toInjection.comp g.bottomHalf.toSurjection).circles := by
    rw [comp_eq_refactorization, circles_comp_of_stringInjective _
        ((stringInjective_injection _).comp g.topHalf.stringInjective_toInjection),
      circles_comp_of_stringSurjective _ f.bottomHalf.stringSurjective_toSurjection,
      circles_comp_of_stringInjective _ g.topHalf.stringInjective_toInjection]; simp
  rw [← hmid, HalfDiagram.toSurjection_comp_toInjection, HalfDiagram.toSurjection_comp_toInjection,
    glue_bottomHalf_topHalf, glue_bottomHalf_topHalf, circles_comp, circles_comp]; simp

/-- **Cellular multiplication of glued half-diagrams at top through-strand count.** When two glued
diagrams `⟨B₁.glue T₁, c₁⟩ : n → m` and `⟨B₂.glue T₂, c₂⟩ : m → p` each have `k` through strands
and the middle pairing `T₁.toInjection ≫ B₂.toSurjection : k → k` preserves all `k` strands, their
composite is `B₁.glue T₂` carrying `c₁ + c₂ + (T₁.toInjection ≫ B₂.toSurjection).circles` closed
circles. -/
theorem glue_comp_glue_of_through_eq (B₁ : HalfDiagram n k) (T₁ : HalfDiagram m k)
    (B₂ : HalfDiagram m k) (T₂ : HalfDiagram p k) (c₁ c₂ : ℕ)
    (hk : (T₁.toInjection.comp B₂.toSurjection).through = k) :
    (⟨B₁.glue T₁, c₁⟩ : TLDiagram n m).comp ⟨B₂.glue T₂, c₂⟩ =
      ⟨B₁.glue T₂, c₁ + c₂ + (T₁.toInjection.comp B₂.toSurjection).circles⟩ := by
  have h₁ : (⟨B₁.glue T₁, c₁⟩ : TLDiagram n m) =
      (⟨PlanarMatching.nested n, c₁⟩ : TLDiagram n n).comp (B₁.toSurjection.comp T₁.toInjection) :=
    by simp
  have h₂ : (⟨B₂.glue T₂, c₂⟩ : TLDiagram m p) =
      (B₂.toSurjection.comp T₂.toInjection).comp ⟨PlanarMatching.nested p, c₂⟩ := by simp
  set c := (T₁.toInjection.comp B₂.toSurjection).circles
  have hmid : (B₁.toSurjection.comp T₁.toInjection).comp (B₂.toSurjection.comp T₂.toInjection) =
      ⟨B₁.glue T₂, c⟩ := by
    have hcomp : B₁.toSurjection.comp ⟨T₂.toInjection.matching, c⟩ =
        (B₁.toSurjection.comp T₂.toInjection).comp ⟨PlanarMatching.nested p, c⟩ := by
      rw [comp_assoc, comp_mk_nested, HalfDiagram.circles_toInjection, zero_add]
    rw [comp_assoc, ← comp_assoc T₁.toInjection B₂.toSurjection T₂.toInjection,
      eq_mk_nested_of_through_eq hk, mk_nested_comp, HalfDiagram.circles_toInjection, add_zero,
      hcomp, B₁.toSurjection_comp_toInjection T₂, comp_mk_nested, zero_add]
  rw [h₁, h₂, comp_assoc, ← comp_assoc (B₁.toSurjection.comp T₁.toInjection), hmid]
  ext : 1
  · simp
  · simp only [mk_nested_comp, comp_mk_nested]; omega

/-! ### Self-pairing, cancellation, and two-sided inverses -/

/-- Composing a string-injective diagram `D : n → m` with its vertical reflection `m → n` yields
the identity matching on `n` strands with `2 * D.circles + (m - n) / 2` closed circles. -/
theorem comp_verticalReflect_of_stringInjective {D : TLDiagram n m} (hD : D.StringInjective) :
    D.comp (verticalReflect n m D) =
      ⟨PlanarMatching.nested n, 2 * D.circles + (m - n) / 2⟩ := by
  induction hD using StringInjective.induction with
  | base c =>
    rw [verticalReflect_mk_nested, comp_mk_nested]
    exact TLDiagram.ext rfl (by dsimp only; omega)
  | step D' hD' c ih =>
    have hmid : (⟨PlanarMatching.nested _, 1⟩ : TLDiagram _ _).comp (verticalReflect n _ D') =
        (verticalReflect n _ D').comp ⟨PlanarMatching.nested n, 1⟩ := by
      rw [mk_nested_comp, comp_mk_nested, add_comm]
    have hcirc' : (D'.comp (cupAt c)).circles = D'.circles := by
      rw [comp_cupAt, circles_insertTopArc]
    rw [verticalReflect_comp, verticalReflect_cupAt, comp_assoc, ← comp_assoc (cupAt c) (capAt c),
      cupAt_comp_capAt, hmid, ← comp_assoc, ih, comp_mk_nested, hcirc']
    exact TLDiagram.ext rfl (by dsimp only; have := hD'.le; omega)

/-- Pre-composing a string-surjective diagram `D : n → m` with its vertical reflection `m → n`
yields the identity matching on `m` strands with `2 * D.circles + (n - m) / 2` closed circles. -/
theorem verticalReflect_comp_of_stringSurjective {D : TLDiagram n m} (hD : D.StringSurjective) :
    (verticalReflect n m D).comp D =
      ⟨PlanarMatching.nested m, 2 * D.circles + (n - m) / 2⟩ := by
  simpa using comp_verticalReflect_of_stringInjective hD.verticalReflect

/-- Post-composition by a string-injective diagram is injective on diagrams from any `n`. -/
theorem StringInjective.eq_of_comp_eq {g : TLDiagram m p} (hg : g.StringInjective)
    {f₁ f₂ : TLDiagram n m} (h : f₁.comp g = f₂.comp g) : f₁ = f₂ := by
  have hr := congrArg (fun x => x.comp (TLDiagram.verticalReflect m p g)) h
  rw [comp_assoc, comp_assoc, comp_verticalReflect_of_stringInjective hg,
    comp_mk_nested, comp_mk_nested] at hr
  obtain ⟨hm, hc⟩ := TLDiagram.mk.inj hr
  exact TLDiagram.ext hm (Nat.add_right_cancel hc)

/-- Pre-composition by a string-surjective diagram is injective on diagrams to any `p`. -/
theorem StringSurjective.eq_of_comp_eq {f : TLDiagram n m} (hf : f.StringSurjective)
    {g₁ g₂ : TLDiagram m p} (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  (TLDiagram.verticalReflect m p).injective <| hf.verticalReflect.eq_of_comp_eq <| by
    rw [← verticalReflect_comp, ← verticalReflect_comp, h]

/-- Any diagram `g : m → p` that is not string-injective fails to cancel on the right, witnessed by
two distinct endomorphisms of `m`. -/
theorem exists_ne_comp_eq_of_not_stringInjective {g : TLDiagram m p}
    (hg : ¬ g.StringInjective) :
    ∃ f₁ f₂ : TLDiagram m m, f₁ ≠ f₂ ∧ f₁.comp g = f₂.comp g := by
  have hlt : g.through < m := lt_of_le_of_ne g.through_le_bottom hg
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 :=
    ⟨m - 2, by have := Nat.even_iff.mp g.even_bottom_sub_through; omega⟩
  obtain ⟨c, hc⟩ := g.bottomHalf.exists_apply_castSucc_eq_succ hlt.ne
  obtain ⟨g', -, -, rfl⟩ := exists_capAt_comp_of_bottomHalf_apply_eq hc
  refine ⟨(capAt c).comp (cupAt c), ⟨PlanarMatching.nested (q + 2), 1⟩, fun heq => ?_, by
    rw [← comp_assoc, ← comp_assoc]; congr 1; simp [comp_assoc]⟩
  have hcirc := congrArg TLDiagram.circles heq
  rw [circles_comp_of_stringInjective _ (stringInjective_cupAt c), circles_capAt,
    circles_cupAt] at hcirc
  dsimp only at hcirc; omega

/-- Any diagram `f : n → m` that is not string-surjective fails to cancel on the left, witnessed by
two distinct endomorphisms of `m`. -/
theorem exists_ne_comp_eq_of_not_stringSurjective {f : TLDiagram n m}
    (hf : ¬ f.StringSurjective) :
    ∃ g₁ g₂ : TLDiagram m m, g₁ ≠ g₂ ∧ f.comp g₁ = f.comp g₂ := by
  obtain ⟨h₁, h₂, hne, heq⟩ := exists_ne_comp_eq_of_not_stringInjective
    (mt stringInjective_verticalReflect_iff.mp hf)
  refine ⟨verticalReflect m m h₁, verticalReflect m m h₂, (verticalReflect m m).injective.ne hne,
    (verticalReflect n m).injective ?_⟩
  rw [verticalReflect_comp, verticalReflect_comp, verticalReflect_verticalReflect,
    verticalReflect_verticalReflect, heq]

/-- **Characterization of right-cancellative diagrams**: `g : m → p` cancels on the right against
all diagrams if and only if `g` is string-injective (see also
`TauCeti.TLDiagram.exists_ne_comp_eq_of_not_stringInjective` for the endomorphism witness). -/
theorem stringInjective_iff_comp_left_injective {g : TLDiagram m p} :
    g.StringInjective ↔ ∀ ⦃n : ℕ⦄, Function.Injective (fun f : TLDiagram n m => f.comp g) :=
  ⟨fun hg _ _ _ h => hg.eq_of_comp_eq h, fun h => by
    by_contra hg
    obtain ⟨f₁, f₂, hne, heq⟩ := exists_ne_comp_eq_of_not_stringInjective hg
    exact hne (h heq)⟩

/-- **Characterization of left-cancellative diagrams**: `f : n → m` cancels on the left against
all diagrams if and only if `f` is string-surjective (see also
`TauCeti.TLDiagram.exists_ne_comp_eq_of_not_stringSurjective` for the endomorphism witness). -/
theorem stringSurjective_iff_comp_right_injective {f : TLDiagram n m} :
    f.StringSurjective ↔ ∀ ⦃p : ℕ⦄, Function.Injective (fun g : TLDiagram m p => f.comp g) :=
  ⟨fun hf _ _ _ h => hf.eq_of_comp_eq h, fun h => by
    by_contra hf
    obtain ⟨g₁, g₂, hne, heq⟩ := exists_ne_comp_eq_of_not_stringSurjective hf
    exact hne (h heq)⟩

/-- Two-sided inverse diagrams force equal boundary counts. -/
theorem eq_of_comp_eq_id {f : TLDiagram n m} {g : TLDiagram m n}
    (h₁ : f.comp g = id n) (h₂ : g.comp f = id m) : n = m :=
  have le_of {a b : ℕ} {x : TLDiagram a b} {y : TLDiagram b a} (h : x.comp y = id a) : a ≤ b :=
    (through_id a).symm.trans_le <| (congrArg TLDiagram.through h).symm.trans_le
      ((through_comp_le_left x y).trans x.through_le_top)
  le_antisymm (le_of h₁) (le_of h₂)

/-- **The only right-invertible endomorphism diagram is the identity**: if `f ≫ g = id n`, then
`f = id n`. -/
theorem eq_id_of_comp_eq_id {f g : TLDiagram n n} (h : f.comp g = id n) : f = id n := by
  have hth : f.through = n := le_antisymm f.through_le_bottom <|
    (through_id n).symm.trans_le ((congrArg TLDiagram.through h).symm.trans_le
      (through_comp_le_left f g))
  have hc := congrArg TLDiagram.circles h
  rw [circles_comp, circles_id] at hc
  rw [eq_mk_nested_of_through_eq hth, show f.circles = 0 by omega]
  ext <;> simp

/-- The Temperley–Lieb generator `e₁ = cap ≫ cup : 2 → 2` has `0` through strands, canonical
surjection `cap : 2 → 0`, and canonical injection `cup : 0 → 2`. -/
example :
    (⟨(cap.comp cup).through, (cap.comp cup).surjection, (cap.comp cup).injection⟩ :
      Σ k : ℕ, TLDiagram 2 k × TLDiagram k 2) = ⟨0, cap, cup⟩ :=
  (existsUnique_factorization (cap.comp cup)).unique
    ⟨(cap.comp cup).stringSurjective_surjection, (cap.comp cup).stringInjective_injection,
      (cap.comp cup).circles_injection, (cap.comp cup).surjection_comp_injection⟩
    ⟨stringSurjective_zero_right cap, stringInjective_zero_left cup, circles_cup, rfl⟩

/-- While `cap : 2 → 0` is string-surjective (hence left-cancellative), it is not string-injective
and fails right-cancellation: `(cap ≫ cup) ≫ cap = ⟨nested 2, 1⟩ ≫ cap` even though `cap ≫ cup`
has `0` circles and `⟨nested 2, 1⟩` has `1`. -/
example : ((cap.comp cup).comp cap) =
    (⟨PlanarMatching.nested 2, 1⟩ : TLDiagram 2 2).comp cap ∧
    cap.comp cup ≠ ⟨PlanarMatching.nested 2, 1⟩ :=
  ⟨by simp [comp_assoc, cup_comp_cap], fun h => by
    have hc := congrArg TLDiagram.circles h
    rw [circles_comp_of_stringInjective _ (stringInjective_zero_left cup), circles_cap,
      circles_cup] at hc
    dsimp only at hc; omega⟩

end TLDiagram

end TauCeti
