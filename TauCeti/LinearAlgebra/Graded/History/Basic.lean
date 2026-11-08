/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Algebra.DirectSum.Component
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Homogeneous histories along paths

Every vertex of a quiver carries a module with an internal direct-sum decomposition,
and every arrow carries a linear map. A degree history selects the whole homogeneous
component after each arrow. The modules and degree sets may vary between vertices.
Concatenation composes histories, and an inserted identity retains only the previously
selected degree. These operations describe successive homogeneous coefficient transfers.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
`Mei/LinearAlgebra/GradedModule/History/Path.lean`.
-/

public noncomputable section

open TauCeti

universe u v w x y

namespace Quiver.Path

variable {Q : Type x} [Quiver.{y} Q] {a : Q}

/-- A degree history of a path: a degree of the target of each arrow, the latest arrow
last. The type computes to a pair for `p.cons e`, so that histories can be extended
one arrow at a time. -/
abbrev Degrees (ι : Q → Type w) : {b : Q} → Path a b → Type w
  | _, nil => PUnit
  | _, @cons _ _ _ _ c p _ => Degrees ι p × ι c

variable {ι : Q → Type w}

/-- The last selected degree, or the prescribed incoming degree for an empty path.
This index is reducible so the degree of a lifted path endpoint reduces without casts. -/
abbrev Degrees.terminalDegree (i₀ : ι a) : {b : Q} → (p : Path a b) → p.Degrees ι → ι b
  | _, nil, _ => i₀
  | _, cons _ _, d => d.2

/-- Empty histories retain the incoming degree. -/
theorem Degrees.terminalDegree_nil (i₀ : ι a) (d : (nil : Path a a).Degrees ι) :
    Degrees.terminalDegree i₀ nil d = i₀ := (rfl)

/-- A nonempty history ends in its last selected degree. -/
theorem Degrees.terminalDegree_cons (i₀ : ι a) {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) :
    Degrees.terminalDegree i₀ (p.cons e) (d, i) = i := (rfl)

/-- Degree histories have decidable equality when the degree types do. -/
instance decidableEqDegrees [∀ q, DecidableEq (ι q)] :
    ∀ {b : Q} (p : Path a b), DecidableEq (p.Degrees ι)
  | _, nil => inferInstanceAs (DecidableEq PUnit)
  | _, cons p _ => @instDecidableEqProd _ _ (decidableEqDegrees p) _

/-- A degree history of a concatenation is a pair of degree histories. -/
def degreesComp {b : Q} (p : Path a b) :
    ∀ {c : Q} (q : Path b c), (p.comp q).Degrees ι ≃ p.Degrees ι × q.Degrees ι
  | _, nil => (Equiv.prodPUnit _).symm
  | _, cons q _ => ((degreesComp p q).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

/-- Concatenating with the empty path appends the trivial history. Not a simp lemma:
simp already normalizes `p.comp nil` in the type of the equivalence. -/
theorem degreesComp_nil {b : Q} (p : Path a b) (d : (p.comp nil).Degrees ι) :
    degreesComp (ι := ι) p (nil : Path b b) d = (d, PUnit.unit) := (rfl)

/-- Splitting off an empty second block does not alter the first history. -/
theorem degreesComp_symm_nil {b : Q} (p : Path a b) (d : p.Degrees ι) (u : PUnit) :
    (degreesComp (ι := ι) p (nil : Path b b)).symm (d, u) = d := (rfl)

/-- Concatenating with a path ending in an arrow splits off its last degree. -/
theorem degreesComp_cons {b c e : Q} (p : Path a b) (q : Path b c) (f : c ⟶ e)
    (d : (p.comp q).Degrees ι) (i : ι e) :
    degreesComp (ι := ι) p (q.cons f) ((d, i) : ((p.comp q).cons f).Degrees ι) =
      ((degreesComp (ι := ι) p q d).1, ((degreesComp (ι := ι) p q d).2, i)) := (rfl)

/-- Joining two histories appends the last selected degree of the second block. -/
theorem degreesComp_symm_cons {b c e : Q} (p : Path a b) (q : Path b c) (f : c ⟶ e)
    (d : p.Degrees ι) (d' : q.Degrees ι) (i : ι e) :
    (degreesComp (ι := ι) p (q.cons f)).symm (d, (d', i)) =
      (((degreesComp (ι := ι) p q).symm (d, d'), i) : ((p.comp q).cons f).Degrees ι) := (rfl)

/-- The terminal degree of a concatenation is the terminal degree of its second
block, starting at the degree reached by its first block. -/
@[simp]
theorem Degrees.terminalDegree_comp (i₀ : ι a) {b c : Q}
    (p : Path a b) (q : Path b c) (d : p.Degrees ι) (e : q.Degrees ι) :
    Degrees.terminalDegree i₀ (p.comp q) ((degreesComp (ι := ι) p q).symm (d, e)) =
      Degrees.terminalDegree (Degrees.terminalDegree i₀ p d) q e := by
  cases q <;> rfl

section Linear

variable {R : Type u} [Semiring R]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)

/-- The composite of the arrow maps along a path: Mathlib's `composePath` of the image of
the path in semimodules. The latest arrow acts last. -/
def composeLinear {b : Q} (p : Path a b) : M a →ₗ[R] M b :=
  (CategoryTheory.composePath
    (({ obj q := SemimoduleCat.of R (M q), map e := SemimoduleCat.ofHom (T e) } :
      Q ⥤q SemimoduleCat.{v} R).mapPath p)).hom

@[simp]
theorem composeLinear_nil : (nil : Path a a).composeLinear T = LinearMap.id := (rfl)

@[simp]
theorem composeLinear_cons {b c : Q} (p : Path a b) (e : b ⟶ c) :
    (p.cons e).composeLinear T = (T e).comp (p.composeLinear T) := (rfl)

/-- The composite along a concatenation is the composite of the two composites. -/
@[simp]
theorem composeLinear_comp {b c : Q} (p : Path a b) (q : Path b c) :
    (p.comp q).composeLinear T = (q.composeLinear T).comp (p.composeLinear T) := by
  rw [composeLinear, Prefunctor.mapPath_comp, CategoryTheory.composePath_comp,
    SemimoduleCat.hom_comp]
  rfl

variable {ι : Q → Type w} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]

/-- Propagation along a path, keeping only the selected homogeneous component after each
arrow. The empty path leaves the input unchanged. -/
def homogeneousHistory : {b : Q} → (p : Path a b) → p.Degrees ι → M a →ₗ[R] M b
  | _, nil, _ => LinearMap.id
  | _, cons p e, d =>
    (homogeneousComponent (ℳ _) d.2).comp ((T e).comp (homogeneousHistory p d.1))

@[simp]
theorem homogeneousHistory_nil (d : (nil : Path a a).Degrees ι) :
    (nil : Path a a).homogeneousHistory T ℳ d = LinearMap.id := (rfl)

/-- One more arrow applies its map to the history and selects the whole component of
the recorded degree. -/
theorem homogeneousHistory_cons {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) =
      (homogeneousComponent (ℳ c) i).comp ((T e).comp (p.homogeneousHistory T ℳ d)) :=
  (rfl)

theorem homogeneousHistory_cons_apply {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) (x : M a) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x =
      (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x)) i : M c) := by
  rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply,
    homogeneousComponent_apply]

/-- The output of a nonempty history lies in its last selected homogeneous piece. -/
theorem homogeneousHistory_cons_mem {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) (x : M a) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ∈ ℳ c i := by
  rw [homogeneousHistory_cons, LinearMap.comp_apply]
  exact homogeneousComponent_mem (ℳ c) i _

section

variable {T ℳ}

/-- The selected output remains homogeneous, including the unchanged incoming
piece when the path is empty. -/
theorem homogeneousHistory_mem_vertex {b : Q} (p : Path a b)
    (d : p.Degrees ι) (i₀ : ι a) (x : M a) (hx : x ∈ ℳ a i₀) :
    p.homogeneousHistory T ℳ d x ∈ ℳ b (Degrees.terminalDegree i₀ p d) := by
  cases p with
  | nil =>
    simpa only [homogeneousHistory_nil, LinearMap.id_apply, Degrees.terminalDegree_nil] using hx
  | cons p e => exact homogeneousHistory_cons_mem T ℳ p e d.1 d.2 x

end

/-- A vanished intermediate decoration cannot yield a nonzero final history. -/
theorem homogeneousHistory_ne_zero_of_cons {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) {x : M a}
    (h : (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ≠ 0) :
    p.homogeneousHistory T ℳ d x ≠ 0 := by
  intro hz
  apply h
  rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero,
    map_zero]

/-- Selecting the terminal degree of a nonempty history returns that history. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory_cons {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    (homogeneousComponent (ℳ c) i).comp
        ((p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)) =
      (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) := by
  ext x
  exact homogeneousComponent_apply_of_mem (ℳ c) (homogeneousHistory_cons_mem T ℳ p e d i x)

/-- A nonempty history has no component in a degree other than its terminal degree. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory_cons_of_ne {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (i η : ι c) (h : i ≠ η) :
    (homogeneousComponent (ℳ c) η).comp
        ((p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)) = 0 := by
  ext x
  exact homogeneousComponent_apply_of_mem_ne (ℳ c) (homogeneousHistory_cons_mem T ℳ p e d i x) h

/-- An arrow carrying the identity selects a component of the previous decoration. -/
theorem homogeneousHistory_cons_of_eq_id {b : Q} (p : Path a b) (e : b ⟶ b)
    (he : T e = LinearMap.id) (d : p.Degrees ι) (i : ι b) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) =
      (homogeneousComponent (ℳ b) i).comp (p.homogeneousHistory T ℳ d) := by
  rw [homogeneousHistory_cons, he, LinearMap.id_comp]

/-- Inserting an identity arrow after a nonempty history keeps that history in its
terminal degree and kills it in every other degree. -/
theorem homogeneousHistory_cons_cons_of_eq_id {b c : Q} (p : Path a b) (e : b ⟶ c)
    (e' : c ⟶ c) (he : T e' = LinearMap.id) (d : p.Degrees ι) (i η : ι c) :
    ((p.cons e).cons e').homogeneousHistory T ℳ
        (((d, i), η) : ((p.cons e).cons e').Degrees ι) =
      if i = η then (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)
      else 0 := by
  rw [homogeneousHistory_cons_of_eq_id T ℳ _ e' he]
  split_ifs with h
  · subst h
    exact homogeneousComponent_comp_homogeneousHistory_cons T ℳ p e d i
  · exact homogeneousComponent_comp_homogeneousHistory_cons_of_ne T ℳ p e d i η h

/-- Along a concatenation, the history of a pair of degree histories is the composite of
the two histories. -/
theorem homogeneousHistory_comp {b : Q} (p : Path a b) :
    ∀ {c : Q} (q : Path b c) (d : p.Degrees ι) (d' : q.Degrees ι),
      (p.comp q).homogeneousHistory T ℳ ((degreesComp (ι := ι) p q).symm (d, d')) =
        (q.homogeneousHistory T ℳ d').comp (p.homogeneousHistory T ℳ d)
  | _, nil, d, _ => (LinearMap.id_comp _).symm
  | _, cons q e, d, d' => by
    calc _ = (homogeneousComponent (ℳ _) d'.2).comp ((T e).comp
          ((p.comp q).homogeneousHistory T ℳ ((degreesComp (ι := ι) p q).symm (d, d'.1)))) :=
        homogeneousHistory_cons T ℳ (p.comp q) e _ d'.2
      _ = _ := by
        rw [homogeneousHistory_comp p q d d'.1, homogeneousHistory_cons T ℳ q e d'.1 d'.2]
        rfl

/-- A finite family of degree-history pairs reindexes to histories of the
concatenated path. The second block acts on the output of the first, and the
family may impose any condition on either block by its choice of pairs. -/
theorem sum_homogeneousHistory_comp {b c : Q} (p : Path a b) (q : Path b c)
    (S : Finset (p.Degrees ι × q.Degrees ι)) :
    ∑ d ∈ S.map (degreesComp (ι := ι) p q).symm.toEmbedding,
      (p.comp q).homogeneousHistory T ℳ d =
      ∑ d ∈ S, (q.homogeneousHistory T ℳ d.2).comp
        (p.homogeneousHistory T ℳ d.1) := by
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun ⟨d, d'⟩ _ => ?_
  exact homogeneousHistory_comp T ℳ p q d d'

end Linear

end Quiver.Path
