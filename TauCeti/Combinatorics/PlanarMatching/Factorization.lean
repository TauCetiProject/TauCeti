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
   `TauCeti.TLDiagram.bottomHalf_comp_of_stringInjective_val`); dual statements for pre-composing
   with a string-surjective diagram follow by vertical reflection.
3. Every diagram `D : n → m` factors through `D.through` as `D.surjection.comp D.injection = D`
   (`TauCeti.TLDiagram.surjection_comp_injection`), where `D.surjection` is string-surjective and
   carries `D.circles`, while `D.injection` is string-injective and circle-free. This factorization
   is unique (`TauCeti.TLDiagram.existsUnique_factorization`).
4. **Re-factorization** (`TauCeti.TLDiagram.refactorization`) computes the canonical factorization
   of `(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` by re-factoring the middle composite `i₁ ≫ s₂`, yielding monotonic
   filtration bounds `(f ≫ g).through ≤ min f.through g.through` and the cellular multiplication
   formula (`TauCeti.TLDiagram.glue_comp_glue_of_through_eq`).
5. **Cancellation and invertibility**: a diagram is left-cancellative (monic) if and only if it is
   string-injective (`TauCeti.TLDiagram.stringInjective_iff_comp_injective`), right-cancellative
   (epic) if and only if it is string-surjective
   (`TauCeti.TLDiagram.stringSurjective_iff_comp_injective`), and two-sided invertible if and only
   if it is an identity diagram (`TauCeti.TLDiagram.eq_id_of_comp_eq_id`).

## Main definitions

* `TauCeti.TLDiagram.StringInjective`, `TauCeti.TLDiagram.StringSurjective`: diagrams whose bottom
  (resp. top) points all lie on through strands.
* `TauCeti.HalfDiagram.toSurjection`, `TauCeti.HalfDiagram.toInjection`: circle-free string
  surjections and injections built by gluing a half-diagram to `HalfDiagram.id k`.
* `TauCeti.TLDiagram.surjection`, `TauCeti.TLDiagram.injection`: the canonical surjective and
  injective factors of a diagram `D` through `D.through`.

## Main results

* `TauCeti.TLDiagram.surjection_comp_injection`, `TauCeti.TLDiagram.existsUnique_factorization`:
  existence and uniqueness of through-strand factorization.
* `TauCeti.TLDiagram.refactorization`, `TauCeti.TLDiagram.through_comp_eq`,
  `TauCeti.TLDiagram.circles_comp_eq`, `TauCeti.TLDiagram.glue_comp_glue_of_through_eq`:
  re-factorization, filtration of through strands, and cellular multiplication.
* `TauCeti.TLDiagram.stringInjective_iff_comp_injective`,
  `TauCeti.TLDiagram.stringSurjective_iff_comp_injective`: combinatorial characterization of
  cancellative diagrams.
* `TauCeti.TLDiagram.eq_id_of_comp_eq_id`: the only two-sided invertible diagrams are identities.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. **123** (1996), 1–34.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

open Equiv

namespace TauCeti

/-! ### Circle-independence of cuts and gluing with circles -/

namespace TLDiagram

variable {n m p q k k₁ k₂ : ℕ}

/-- Equal diagrams have the same underlying bottom half-diagram permutation. -/
theorem bottomHalf_val_congr {D E : TLDiagram n m} (h : D = E) :
    D.bottomHalf.val = E.bottomHalf.val := by
  subst h; rfl

/-- Equal diagrams have the same underlying top half-diagram permutation. -/
theorem topHalf_val_congr {D E : TLDiagram n m} (h : D = E) :
    D.topHalf.val = E.topHalf.val := by
  subst h; rfl

/-- Stored circles do not affect the number of through strands. -/
theorem through_mk_eq (x : PlanarMatching (n + m)) (c d : ℕ) :
    (TLDiagram.mk x c).through = (TLDiagram.mk x d).through := by
  simp only [through_def]

/-- Stored circles do not affect the underlying bottom half-diagram permutation. -/
theorem bottomHalf_mk_val_eq (x : PlanarMatching (n + m)) (c d : ℕ) :
    (TLDiagram.mk x c).bottomHalf.val = (TLDiagram.mk x d).bottomHalf.val := by
  ext i
  simp only [bottomHalf_apply]

/-- Stored circles do not affect the underlying top half-diagram permutation. -/
theorem topHalf_mk_val_eq (x : PlanarMatching (n + m)) (c d : ℕ) :
    (TLDiagram.mk x c).topHalf.val = (TLDiagram.mk x d).topHalf.val := by
  rw [topHalf_val, topHalf_val]
  ext i
  simp only [bottomHalf_apply, matching_verticalReflect]

@[simp]
theorem through_glue_mk (B : HalfDiagram n k) (T : HalfDiagram m k) (c : ℕ) :
    (TLDiagram.mk (B.glue T) c).through = k :=
  (through_mk_eq (B.glue T) c 0).trans (B.through_glue T)

@[simp]
theorem bottomHalf_glue_mk_val (B : HalfDiagram n k) (T : HalfDiagram m k) (c : ℕ) :
    (TLDiagram.mk (B.glue T) c).bottomHalf.val = B.val :=
  (bottomHalf_mk_val_eq (B.glue T) c 0).trans (B.bottomHalf_glue_val T)

@[simp]
theorem topHalf_glue_mk_val (B : HalfDiagram n k) (T : HalfDiagram m k) (c : ℕ) :
    (TLDiagram.mk (B.glue T) c).topHalf.val = T.val :=
  (topHalf_mk_val_eq (B.glue T) c 0).trans (B.topHalf_glue_val T)

/-- Gluing the bottom and top half-diagrams of `D` recovers `D.matching`. -/
@[simp]
theorem glue_bottomHalf_topHalf (D : TLDiagram n m) :
    D.bottomHalf.glue D.topHalf = D.matching :=
  matching_eq_of_halves (D := ⟨D.bottomHalf.glue D.topHalf, 0⟩) (E := D)
    (D.bottomHalf.bottomHalf_glue_val D.topHalf) (D.bottomHalf.topHalf_glue_val D.topHalf)

/-! ### String-injective and string-surjective diagrams -/

/-- A Temperley–Lieb diagram `D : n → m` is **string-injective** if all `n` bottom boundary points
lie on through strands (`D.through = n`), equivalently its bottom half-diagram has no caps. -/
def StringInjective (D : TLDiagram n m) : Prop :=
  D.through = n

/-- A Temperley–Lieb diagram `D : n → m` is **string-surjective** if all `m` top boundary points
lie on through strands (`D.through = m`), equivalently its top half-diagram has no cups. -/
def StringSurjective (D : TLDiagram n m) : Prop :=
  D.through = m

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
    D.StringInjective ↔ D.bottomHalf.val = 1 :=
  HalfDiagram.val_eq_one_iff.symm

/-- A diagram is string-surjective precisely when its top half-diagram has no arcs. -/
theorem stringSurjective_iff_topHalf_val_eq_one {D : TLDiagram n m} :
    D.StringSurjective ↔ D.topHalf.val = 1 :=
  HalfDiagram.val_eq_one_iff.symm

@[simp]
theorem stringSurjective_verticalReflect_iff {D : TLDiagram n m} :
    (verticalReflect n m D).StringSurjective ↔ D.StringInjective := by
  simp [StringSurjective, StringInjective]

@[simp]
theorem stringInjective_verticalReflect_iff {D : TLDiagram n m} :
    (verticalReflect n m D).StringInjective ↔ D.StringSurjective := by
  simp [StringSurjective, StringInjective]

theorem StringInjective.verticalReflect {D : TLDiagram n m} (h : D.StringInjective) :
    (TLDiagram.verticalReflect n m D).StringSurjective :=
  stringSurjective_verticalReflect_iff.mpr h

theorem StringSurjective.verticalReflect {D : TLDiagram n m} (h : D.StringSurjective) :
    (TLDiagram.verticalReflect n m D).StringInjective :=
  stringInjective_verticalReflect_iff.mpr h

@[simp]
theorem stringInjective_id (n : ℕ) : (id n).StringInjective := through_id n

@[simp]
theorem stringSurjective_id (n : ℕ) : (id n).StringSurjective := through_id n

@[simp]
theorem stringInjective_cup : cup.StringInjective := through_zero_left cup

@[simp]
theorem stringSurjective_cap : cap.StringSurjective := through_zero_right cap

@[simp]
theorem stringInjective_cupAt (c : Fin (q + 1)) : (cupAt c).StringInjective := through_cupAt c

@[simp]
theorem stringSurjective_capAt (c : Fin (q + 1)) : (capAt c).StringSurjective := through_capAt c

/-- An endomorphism diagram `n → n` whose strands all go through has the fully nested identity
matching. -/
theorem matching_eq_nested_of_through_eq {D : TLDiagram n n} (h : D.through = n) :
    D.matching = PlanarMatching.nested n :=
  (matching_eq_of_halves (D := D) (E := id n)
    ((HalfDiagram.val_eq_one_iff.mpr h).trans (bottomHalf_id_val n).symm)
    ((HalfDiagram.val_eq_one_iff.mpr h).trans (topHalf_id_val n).symm)).trans (matching_id n)

/-- An endomorphism diagram `n → n` whose strands all go through is the identity matching together
with its closed circles. -/
theorem eq_mk_nested_of_through_eq {D : TLDiagram n n} (h : D.through = n) :
    D = ⟨PlanarMatching.nested n, D.circles⟩ :=
  TLDiagram.ext (matching_eq_nested_of_through_eq h) rfl

end TLDiagram

/-! ### Embedding half-diagrams and canonical through-strand factors -/

namespace HalfDiagram

variable {n m k : ℕ}

/-- View a half-diagram `B : HalfDiagram n k` as a circle-free string-surjective diagram `n → k`
by joining its `k` defects in order to the `k` top boundary points. -/
def toSurjection (B : HalfDiagram n k) : TLDiagram n k :=
  ⟨B.glue (HalfDiagram.id k), 0⟩

/-- View a half-diagram `T : HalfDiagram m k` as a circle-free string-injective diagram `k → m`
by joining the `k` bottom boundary points in order to the `k` defects of `T` on the top. -/
def toInjection (T : HalfDiagram m k) : TLDiagram k m :=
  ⟨(HalfDiagram.id k).glue T, 0⟩

@[simp]
theorem matching_toSurjection (B : HalfDiagram n k) :
    B.toSurjection.matching = B.glue (HalfDiagram.id k) := (rfl)

@[simp]
theorem circles_toSurjection (B : HalfDiagram n k) : B.toSurjection.circles = 0 := (rfl)

@[simp]
theorem through_toSurjection (B : HalfDiagram n k) : B.toSurjection.through = k :=
  B.through_glue (HalfDiagram.id k)

@[simp]
theorem bottomHalf_toSurjection_val (B : HalfDiagram n k) :
    B.toSurjection.bottomHalf.val = B.val :=
  B.bottomHalf_glue_val (HalfDiagram.id k)

@[simp]
theorem topHalf_toSurjection_val (B : HalfDiagram n k) : B.toSurjection.topHalf.val = 1 :=
  (B.topHalf_glue_val (HalfDiagram.id k)).trans (HalfDiagram.id_val k)

@[simp]
theorem stringSurjective_toSurjection (B : HalfDiagram n k) :
    B.toSurjection.StringSurjective :=
  B.through_toSurjection

@[simp]
theorem matching_toInjection (T : HalfDiagram m k) :
    T.toInjection.matching = (HalfDiagram.id k).glue T := (rfl)

@[simp]
theorem circles_toInjection (T : HalfDiagram m k) : T.toInjection.circles = 0 := (rfl)

@[simp]
theorem through_toInjection (T : HalfDiagram m k) : T.toInjection.through = k :=
  (HalfDiagram.id k).through_glue T

@[simp]
theorem bottomHalf_toInjection_val (T : HalfDiagram m k) : T.toInjection.bottomHalf.val = 1 :=
  ((HalfDiagram.id k).bottomHalf_glue_val T).trans (HalfDiagram.id_val k)

@[simp]
theorem topHalf_toInjection_val (T : HalfDiagram m k) : T.toInjection.topHalf.val = T.val :=
  (HalfDiagram.id k).topHalf_glue_val T

@[simp]
theorem stringInjective_toInjection (T : HalfDiagram m k) :
    T.toInjection.StringInjective :=
  T.through_toInjection

@[simp]
theorem toSurjection_id (k : ℕ) : (HalfDiagram.id k).toSurjection = TLDiagram.id k :=
  TLDiagram.ext_halves (by simp) (by simp) (by simp)

@[simp]
theorem toInjection_id (k : ℕ) : (HalfDiagram.id k).toInjection = TLDiagram.id k :=
  TLDiagram.ext_halves (by simp) (by simp) (by simp)

@[simp]
theorem verticalReflect_toSurjection (B : HalfDiagram n k) :
    TLDiagram.verticalReflect n k B.toSurjection = B.toInjection :=
  TLDiagram.ext_halves (by rw [← TLDiagram.topHalf_val]; simp) (by simp) (by simp)

@[simp]
theorem verticalReflect_toInjection (T : HalfDiagram m k) :
    TLDiagram.verticalReflect k m T.toInjection = T.toSurjection := by
  rw [← verticalReflect_toSurjection, TLDiagram.verticalReflect_verticalReflect]

theorem toSurjection_injective : Function.Injective (@toSurjection n k) :=
  fun _ _ h => Subtype.ext (by simpa using TLDiagram.bottomHalf_val_congr h)

theorem toInjection_injective : Function.Injective (@toInjection m k) :=
  fun _ _ h => Subtype.ext (by simpa using TLDiagram.topHalf_val_congr h)

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
def injection (D : TLDiagram n m) : TLDiagram D.through m :=
  D.topHalf.toInjection

@[simp]
theorem matching_surjection (D : TLDiagram n m) :
    D.surjection.matching = D.bottomHalf.glue (HalfDiagram.id D.through) := (rfl)

@[simp]
theorem circles_surjection (D : TLDiagram n m) : D.surjection.circles = D.circles := (rfl)

@[simp]
theorem through_surjection (D : TLDiagram n m) : D.surjection.through = D.through :=
  through_glue_mk _ _ _

@[simp]
theorem bottomHalf_surjection_val (D : TLDiagram n m) :
    D.surjection.bottomHalf.val = D.bottomHalf.val :=
  bottomHalf_glue_mk_val _ _ _

@[simp]
theorem topHalf_surjection_val (D : TLDiagram n m) : D.surjection.topHalf.val = 1 :=
  (topHalf_glue_mk_val _ _ _).trans (HalfDiagram.id_val _)

@[simp]
theorem stringSurjective_surjection (D : TLDiagram n m) : D.surjection.StringSurjective :=
  D.through_surjection

@[simp]
theorem matching_injection (D : TLDiagram n m) :
    D.injection.matching = (HalfDiagram.id D.through).glue D.topHalf := (rfl)

@[simp]
theorem circles_injection (D : TLDiagram n m) : D.injection.circles = 0 := (rfl)

@[simp]
theorem through_injection (D : TLDiagram n m) : D.injection.through = D.through :=
  D.topHalf.through_toInjection

@[simp]
theorem bottomHalf_injection_val (D : TLDiagram n m) : D.injection.bottomHalf.val = 1 :=
  D.topHalf.bottomHalf_toInjection_val

@[simp]
theorem topHalf_injection_val (D : TLDiagram n m) : D.injection.topHalf.val = D.topHalf.val :=
  D.topHalf.topHalf_toInjection_val

@[simp]
theorem stringInjective_injection (D : TLDiagram n m) : D.injection.StringInjective :=
  D.through_injection

/-! ### Composition with string injections and surjections -/

private theorem comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) :
    (f.comp g).circles = f.circles + g.circles ∧
      (f.comp g).through = f.through ∧
      (f.comp g).bottomHalf.val = f.bottomHalf.val := by
  suffices ∀ (d : ℕ) {p : ℕ} (g : TLDiagram m p), g.StringInjective → p - m = 2 * d →
      (f.comp g).circles = f.circles + g.circles ∧
        (f.comp g).through = f.through ∧
        (f.comp g).bottomHalf.val = f.bottomHalf.val from
    this ((p - m) / 2) g hg (by have := Nat.even_iff.mp hg.even_sub; omega)
  intro d
  induction d with
  | zero =>
    intro p g hg hd
    have hmp : m = p := le_antisymm hg.le (by omega)
    subst hmp
    rw [eq_mk_nested_of_through_eq hg, comp_mk_nested]
    exact ⟨rfl, through_mk_eq _ _ _, bottomHalf_mk_val_eq _ _ _⟩
  | succ d ih =>
    intro p g hg hd
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hg.le; omega⟩
    have hlt : g.through < q + 2 := by rw [hg.through_eq]; omega
    obtain ⟨c, hc⟩ := g.topHalf.exists_apply_castSucc_eq_succ hlt
    obtain ⟨g', hth', hcirc', rfl⟩ := exists_comp_cupAt_of_topHalf_apply_eq hc
    have hg' : g'.StringInjective := hth'.trans hg
    obtain ⟨ihc, iht, ihb⟩ := ih g' hg' (by have := hg'.le; omega)
    have hassoc : f.comp (g'.comp (cupAt c)) = (f.comp g').insertTopArc c := by
      rw [← comp_assoc, comp_cupAt]
    exact ⟨by rw [hassoc, circles_insertTopArc, ihc, hcirc'],
      by rw [hassoc, through_insertTopArc, iht],
      by rw [bottomHalf_val_congr hassoc, bottomHalf_insertTopArc_val, ihb]⟩

/-- Post-composing with a string-injective diagram closes no new circles in the middle: the total
circle count is simply `f.circles + g.circles`. -/
theorem circles_comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).circles = f.circles + g.circles :=
  (comp_of_stringInjective f hg).1

/-- Post-composing with a string-injective diagram preserves the number of through strands. -/
theorem through_comp_of_stringInjective (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).through = f.through :=
  (comp_of_stringInjective f hg).2.1

/-- Post-composing with a string-injective diagram preserves the bottom half-diagram. -/
theorem bottomHalf_comp_of_stringInjective_val (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.StringInjective) : (f.comp g).bottomHalf.val = f.bottomHalf.val :=
  (comp_of_stringInjective f hg).2.2

/-- Pre-composing with a string-surjective diagram closes no new circles in the middle. -/
theorem circles_comp_of_stringSurjective {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).circles = f.circles + g.circles := by
  rw [← circles_verticalReflect (f.comp g), verticalReflect_comp,
    circles_comp_of_stringInjective _ hf.verticalReflect,
    circles_verticalReflect, circles_verticalReflect, add_comm]

/-- Pre-composing with a string-surjective diagram preserves the number of through strands. -/
theorem through_comp_of_stringSurjective {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).through = g.through := by
  rw [← through_verticalReflect (f.comp g), verticalReflect_comp,
    through_comp_of_stringInjective _ hf.verticalReflect, through_verticalReflect]

/-- Pre-composing with a string-surjective diagram preserves the top half-diagram. -/
theorem topHalf_comp_of_stringSurjective_val {f : TLDiagram n m} (g : TLDiagram m p)
    (hf : f.StringSurjective) : (f.comp g).topHalf.val = g.topHalf.val := by
  rw [topHalf_val, bottomHalf_val_congr (verticalReflect_comp f g),
    bottomHalf_comp_of_stringInjective_val _ hf.verticalReflect, ← topHalf_val]

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
    (by rw [bottomHalf_comp_of_stringInjective_val _ T.stringInjective_toInjection]; simp)
    (by rw [topHalf_comp_of_stringSurjective_val _ B.stringSurjective_toSurjection]; simp)
    (by rw [circles_comp_of_stringInjective _ T.stringInjective_toInjection]; simp)

/-- **Through-strand factorization**: every Temperley–Lieb diagram `D : n → m` is the composite of
its canonical surjective factor `D.surjection : n → D.through` followed by its canonical injective
factor `D.injection : D.through → m`. -/
@[simp]
theorem surjection_comp_injection (D : TLDiagram n m) : D.surjection.comp D.injection = D :=
  ext_halves
    (by rw [bottomHalf_comp_of_stringInjective_val _ D.stringInjective_injection,
          bottomHalf_surjection_val])
    (by rw [topHalf_comp_of_stringSurjective_val _ D.stringSurjective_surjection,
          topHalf_injection_val])
    (by rw [circles_comp_of_stringInjective _ D.stringInjective_injection,
          circles_surjection, circles_injection, add_zero])

/-- Composing a string-surjective diagram `n → k` with a string-injective diagram `k → m` produces
a diagram with exactly `k` through strands. -/
theorem through_comp_of_stringSurjective_of_stringInjective {s : TLDiagram n k}
    {i : TLDiagram k m} (hs : s.StringSurjective) (hi : i.StringInjective) :
    (s.comp i).through = k := by
  rw [through_comp_of_stringInjective s hi, hs.through_eq]

/-- In any factorization `s.comp i = D` into a string-surjective `s : n → k` and a string-injective
`i : k → m`, the intermediate strand count `k` must equal `D.through`. -/
theorem through_eq_of_comp_eq {D : TLDiagram n m} {s : TLDiagram n k} {i : TLDiagram k m}
    (hs : s.StringSurjective) (hi : i.StringInjective) (h : s.comp i = D) :
    k = D.through := by
  rw [← h, through_comp_of_stringSurjective_of_stringInjective hs hi]

/-- Associativity and factorization rewrite `(s₁ ≫ i₁) ≫ (s₂ ≫ i₂)` by re-factoring the middle
composite `i₁ ≫ s₂`. -/
theorem comp_eq_refactorization (s₁ : TLDiagram n k₁) (i₁ : TLDiagram k₁ m)
    (s₂ : TLDiagram m k₂) (i₂ : TLDiagram k₂ p) :
    (s₁.comp i₁).comp (s₂.comp i₂) =
      (s₁.comp (i₁.comp s₂).surjection).comp ((i₁.comp s₂).injection.comp i₂) := by
  symm
  rw [comp_assoc, ← comp_assoc (i₁.comp s₂).surjection, surjection_comp_injection,
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
    (f.comp g).through ≤ f.through := by
  rw [through_comp_eq]
  exact (f.injection.comp g.surjection).through_le_bottom

/-- Composition cannot increase the number of through strands beyond that of the top factor. -/
theorem through_comp_le_right (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).through ≤ g.through := by
  rw [through_comp_eq]
  exact (f.injection.comp g.surjection).through_le_top

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
  have hs : s.StringSurjective :=
    le_antisymm s.through_le_top ((congrArg TLDiagram.through h).symm.trans_le
      (through_comp_le_left s i))
  have hi : i.StringInjective :=
    le_antisymm i.through_le_bottom ((congrArg TLDiagram.through h).symm.trans_le
      (through_comp_le_right s i))
  refine ⟨ext_halves ?_ ?_ ?_, ext_halves ?_ ?_ ?_⟩
  · rw [← bottomHalf_comp_of_stringInjective_val s hi, bottomHalf_val_congr h,
      bottomHalf_surjection_val]
  · rw [stringSurjective_iff_topHalf_val_eq_one.mp hs, topHalf_surjection_val]
  · have hcirc := congrArg TLDiagram.circles h
    rw [circles_comp_of_stringInjective s hi, hc, add_zero] at hcirc
    exact hcirc.trans D.circles_surjection.symm
  · rw [stringInjective_iff_bottomHalf_val_eq_one.mp hi, bottomHalf_injection_val]
  · rw [← topHalf_comp_of_stringSurjective_val i hs, topHalf_val_congr h, topHalf_injection_val]
  · exact hc.trans D.circles_injection.symm

/-- **Existence and uniqueness of through-strand factorization.** Every diagram `D : n → m`
factors through a unique intermediate strand count `k` as a string-surjective diagram `s : n → k`
followed by a circle-free string-injective diagram `i : k → m`, namely `k = D.through`,
`s = D.surjection`, and `i = D.injection`. -/
theorem existsUnique_factorization (D : TLDiagram n m) :
    ∃! p : Σ k : ℕ, TLDiagram n k × TLDiagram k m,
      p.2.1.StringSurjective ∧ p.2.2.StringInjective ∧ p.2.2.circles = 0 ∧
        p.2.1.comp p.2.2 = D := by
  refine ⟨⟨D.through, D.surjection, D.injection⟩,
    ⟨D.stringSurjective_surjection, D.stringInjective_injection, D.circles_injection,
      D.surjection_comp_injection⟩, ?_⟩
  rintro ⟨k, s, i⟩ ⟨hs, hi, hc, hcomp⟩
  have hk : k = D.through := through_eq_of_comp_eq hs hi hcomp
  subst hk
  obtain ⟨rfl, rfl⟩ := eq_surjection_and_eq_injection_of_comp_eq hc hcomp
  rfl

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
  let f₀ : TLDiagram n m := f.bottomHalf.toSurjection.comp f.topHalf.toInjection
  let g₀ : TLDiagram m p := g.bottomHalf.toSurjection.comp g.topHalf.toInjection
  have hf₀ : f₀ = ⟨f.matching, 0⟩ := by
    dsimp only [f₀]; rw [HalfDiagram.toSurjection_comp_toInjection, glue_bottomHalf_topHalf]
  have hg₀ : g₀ = ⟨g.matching, 0⟩ := by
    dsimp only [g₀]; rw [HalfDiagram.toSurjection_comp_toInjection, glue_bottomHalf_topHalf]
  have hmid : (f₀.comp g₀).circles =
      (f.topHalf.toInjection.comp g.bottomHalf.toSurjection).circles := by
    dsimp only [f₀, g₀]
    rw [comp_eq_refactorization,
      circles_comp_of_stringInjective _
        ((stringInjective_injection _).comp g.topHalf.stringInjective_toInjection),
      circles_comp_of_stringSurjective _ f.bottomHalf.stringSurjective_toSurjection,
      circles_comp_of_stringInjective _ g.topHalf.stringInjective_toInjection]
    simp
  rw [circles_comp, ← hmid, hf₀, hg₀, circles_comp]
  simp

/-- **Cellular multiplication of glued half-diagrams at top through-strand count.** When two glued
diagrams `B₁.glue T₁ : n → m` and `B₂.glue T₂ : m → p` each have `k` through strands and the middle
pairing `T₁.toInjection ≫ B₂.toSurjection : k → k` preserves all `k` strands, their composite is
`B₁.glue T₂` carrying `(T₁.toInjection ≫ B₂.toSurjection).circles` closed circles. -/
theorem glue_comp_glue_of_through_eq (B₁ : HalfDiagram n k) (T₁ : HalfDiagram m k)
    (B₂ : HalfDiagram m k) (T₂ : HalfDiagram p k)
    (hk : (T₁.toInjection.comp B₂.toSurjection).through = k) :
    (⟨B₁.glue T₁, 0⟩ : TLDiagram n m).comp ⟨B₂.glue T₂, 0⟩ =
      ⟨B₁.glue T₂, (T₁.toInjection.comp B₂.toSurjection).circles⟩ := by
  set c := (T₁.toInjection.comp B₂.toSurjection).circles
  have hM : T₁.toInjection.comp B₂.toSurjection = ⟨PlanarMatching.nested k, c⟩ :=
    eq_mk_nested_of_through_eq hk
  rw [← B₁.toSurjection_comp_toInjection T₁, ← B₂.toSurjection_comp_toInjection T₂,
    comp_assoc, ← comp_assoc T₁.toInjection B₂.toSurjection T₂.toInjection, hM,
    mk_nested_comp, HalfDiagram.circles_toInjection, add_zero]
  have hcomp : B₁.toSurjection.comp ⟨T₂.toInjection.matching, c⟩ =
      (B₁.toSurjection.comp T₂.toInjection).comp ⟨PlanarMatching.nested p, c⟩ := by
    rw [comp_assoc, comp_mk_nested, HalfDiagram.circles_toInjection, zero_add]
  rw [hcomp, B₁.toSurjection_comp_toInjection T₂, comp_mk_nested, zero_add]

/-! ### Self-pairing, cancellation, and two-sided inverses -/

/-- Composing a string-injective diagram `D : n → m` with its vertical reflection `m → n` yields
the identity matching on `n` strands with `2 * D.circles + (m - n) / 2` closed circles. -/
theorem comp_verticalReflect_of_stringInjective {D : TLDiagram n m} (hD : D.StringInjective) :
    D.comp (verticalReflect n m D) =
      ⟨PlanarMatching.nested n, 2 * D.circles + (m - n) / 2⟩ := by
  suffices ∀ (d : ℕ) {n m : ℕ} (D : TLDiagram n m), D.StringInjective → m - n = 2 * d →
      D.comp (verticalReflect n m D) =
        ⟨PlanarMatching.nested n, 2 * D.circles + (m - n) / 2⟩ from
    this ((m - n) / 2) D hD (by have := Nat.even_iff.mp hD.even_sub; omega)
  intro d
  induction d with
  | zero =>
    intro n m D hD hd
    have hnm : n = m := le_antisymm hD.le (by omega)
    subst hnm
    have hvr : (verticalReflect n n D).through = n := (through_verticalReflect D).trans hD
    rw [eq_mk_nested_of_through_eq hvr, eq_mk_nested_of_through_eq hD, comp_mk_nested,
      circles_verticalReflect]
    ext : 1
    · rfl
    · dsimp only; omega
  | succ d ih =>
    intro n m D hD hd
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by have := hD.le; omega⟩
    obtain ⟨c, hc⟩ := D.topHalf.exists_apply_castSucc_eq_succ (by rw [hD.through_eq]; omega)
    obtain ⟨D', hth', hcirc', rfl⟩ := exists_comp_cupAt_of_topHalf_apply_eq hc
    have hD' : D'.StringInjective := hth'.trans hD
    have ihD := ih D' hD' (by have := hD'.le; omega)
    have hmid : (⟨PlanarMatching.nested q, 1⟩ : TLDiagram q q).comp (verticalReflect n q D') =
        (verticalReflect n q D').comp ⟨PlanarMatching.nested n, 1⟩ := by
      rw [mk_nested_comp, comp_mk_nested, add_comm]
    rw [verticalReflect_comp, verticalReflect_cupAt, comp_assoc,
      ← comp_assoc (cupAt c) (capAt c), cupAt_comp_capAt, hmid, ← comp_assoc, ihD,
      comp_mk_nested, ← hcirc']
    ext : 1
    · rfl
    · dsimp only; have := hD'.le; omega

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
    {g₁ g₂ : TLDiagram m p} (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ := by
  apply (TLDiagram.verticalReflect m p).injective
  refine hf.verticalReflect.eq_of_comp_eq ?_
  rw [← verticalReflect_comp, ← verticalReflect_comp, h]

/-- **The Temperley–Lieb loop-closing relation**: `capAt c ≫ cupAt c ≫ capAt c` equals `capAt c`
with one additional closed circle. -/
theorem capAt_comp_cupAt_comp_capAt (c : Fin (q + 1)) :
    ((capAt c).comp (cupAt c)).comp (capAt c) =
      (⟨PlanarMatching.nested (q + 2), 1⟩ : TLDiagram (q + 2) (q + 2)).comp (capAt c) := by
  simp [comp_assoc]

/-- Dual loop-closing relation: `cupAt c ≫ capAt c ≫ cupAt c` equals `cupAt c` with one additional
closed circle. -/
theorem cupAt_comp_capAt_comp_cupAt (c : Fin (q + 1)) :
    (cupAt c).comp ((capAt c).comp (cupAt c)) =
      (cupAt c).comp ⟨PlanarMatching.nested (q + 2), 1⟩ := by
  simp [← comp_assoc]

/-- Any diagram `g : m → p` that is not string-injective fails to cancel on the right, witnessed by
two distinct endomorphisms of `m`. -/
theorem exists_ne_comp_eq_of_not_stringInjective {g : TLDiagram m p}
    (hg : ¬ g.StringInjective) :
    ∃ f₁ f₂ : TLDiagram m m, f₁ ≠ f₂ ∧ f₁.comp g = f₂.comp g := by
  have hlt : g.through < m := lt_of_le_of_ne g.through_le_bottom hg
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 :=
    ⟨m - 2, by have := Nat.even_iff.mp g.even_bottom_sub_through; omega⟩
  obtain ⟨c, hc⟩ := g.bottomHalf.exists_apply_castSucc_eq_succ hlt
  obtain ⟨g', -, -, rfl⟩ := exists_capAt_comp_of_bottomHalf_apply_eq hc
  refine ⟨(capAt c).comp (cupAt c), ⟨PlanarMatching.nested (q + 2), 1⟩, ?_, ?_⟩
  · intro heq
    have hcirc := congrArg TLDiagram.circles heq
    rw [circles_comp_of_stringInjective _ (stringInjective_cupAt c), circles_capAt,
      circles_cupAt] at hcirc
    dsimp only at hcirc
    omega
  · rw [← comp_assoc, ← comp_assoc, capAt_comp_cupAt_comp_capAt]

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
all diagrams (or just against endomorphisms of `m`) if and only if `g` is string-injective. -/
theorem stringInjective_iff_comp_injective {g : TLDiagram m p} :
    g.StringInjective ↔ ∀ ⦃n : ℕ⦄, Function.Injective (fun f : TLDiagram n m => f.comp g) :=
  ⟨fun hg _ _ _ h => hg.eq_of_comp_eq h, fun h => by
    by_contra hg
    obtain ⟨f₁, f₂, hne, heq⟩ := exists_ne_comp_eq_of_not_stringInjective hg
    exact hne (h heq)⟩

/-- **Characterization of left-cancellative diagrams**: `f : n → m` cancels on the left against
all diagrams (or just against endomorphisms of `m`) if and only if `f` is string-surjective. -/
theorem stringSurjective_iff_comp_injective {f : TLDiagram n m} :
    f.StringSurjective ↔ ∀ ⦃p : ℕ⦄, Function.Injective (fun g : TLDiagram m p => f.comp g) :=
  ⟨fun hf _ _ _ h => hf.eq_of_comp_eq h, fun h => by
    by_contra hf
    obtain ⟨g₁, g₂, hne, heq⟩ := exists_ne_comp_eq_of_not_stringSurjective hf
    exact hne (h heq)⟩

/-- Two-sided inverse diagrams force equal boundary counts. -/
theorem eq_of_comp_eq_id {f : TLDiagram n m} {g : TLDiagram m n}
    (h₁ : f.comp g = id n) (h₂ : g.comp f = id m) : n = m := by
  have hnm : n ≤ m := by
    calc n = (id n).through := (through_id n).symm
      _ = (f.comp g).through := by rw [h₁]
      _ ≤ f.through := through_comp_le_left f g
      _ ≤ m := f.through_le_top
  have hmn : m ≤ n := by
    calc m = (id m).through := (through_id m).symm
      _ = (g.comp f).through := by rw [h₂]
      _ ≤ g.through := through_comp_le_left g f
      _ ≤ n := g.through_le_top
  exact le_antisymm hnm hmn

/-- **The only right-invertible endomorphism diagram is the identity**: if `f ≫ g = id n`, then
`f = id n`. -/
theorem eq_id_of_comp_eq_id {f g : TLDiagram n n} (h : f.comp g = id n) : f = id n := by
  have hth : f.through = n := le_antisymm f.through_le_bottom <| by
    calc n = (id n).through := (through_id n).symm
      _ = (f.comp g).through := by rw [h]
      _ ≤ f.through := through_comp_le_left f g
  have hcirc : f.circles = 0 := by
    have hc := congrArg TLDiagram.circles h
    rw [circles_comp, circles_id] at hc
    omega
  rw [eq_mk_nested_of_through_eq hth, hcirc]
  ext <;> simp

/-- The Temperley–Lieb generator `e₁ = cap ≫ cup : 2 → 2` has `0` through strands, canonical
surjection `cap : 2 → 0`, and canonical injection `cup : 0 → 2`. -/
example : (cap.comp cup).through = 0 := by
  rw [through_comp_of_stringInjective cap stringInjective_cup, through_zero_right]

/-- While `cap : 2 → 0` is string-surjective (hence left-cancellative), it is not string-injective
and fails right-cancellation: `(cap ≫ cup) ≫ cap = ⟨nested 2, 1⟩ ≫ cap` even though `cap ≫ cup`
has `0` circles and `⟨nested 2, 1⟩` has `1`. -/
example : ((cap.comp cup).comp cap) =
    (⟨PlanarMatching.nested 2, 1⟩ : TLDiagram 2 2).comp cap ∧
    cap.comp cup ≠ ⟨PlanarMatching.nested 2, 1⟩ := by
  refine ⟨?_, ?_⟩
  · simpa using capAt_comp_cupAt_comp_capAt (0 : Fin 1)
  · intro h
    have hc := congrArg TLDiagram.circles h
    rw [circles_comp_of_stringInjective _ stringInjective_cup, circles_cap, circles_cup] at hc
    dsimp only at hc
    omega

end TLDiagram

end TauCeti
