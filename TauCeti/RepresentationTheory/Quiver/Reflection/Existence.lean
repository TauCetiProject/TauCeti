/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.PositiveRoot
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Composite
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Uniqueness

/-!
# Every positive root is the dimension vector of an indecomposable representation

Let `Q` be a finite acyclic quiver whose Tits form is positive definite, the numerical side of the
ADE condition in Gabriel's theorem. `TauCeti.titsForm_dimVector_eq_one_of_indecomposable` sends a
finite-dimensional indecomposable representation of `Q` to a positive root of the Tits form, and
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable` shows that map injective on isomorphism
classes. This file proves it **surjective**: every positive root is realized
(`TauCeti.exists_indecomposable_dimVector_eq`), so `M ↦ dim M` is a bijection from the isomorphism
classes of finite-dimensional indecomposables onto the positive roots. No algebraic closedness is
needed anywhere: the Bernstein-Gelfand-Ponomarev reflection functors work over any field.

## The argument

The injective half runs the sink reflection functors forwards until they annihilate the
representation; the surjective half runs the *source* reflection functors backwards from a vertex
simple, and the word to run them along is the one the Weyl-orbit reduction supplies.

1. *One word.* `TauCeti.exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg` carries a
   positive root `d` to a simple root by finitely many full passes of a sink-admissible ordering `l`
   followed by an initial segment of `l`, with every intermediate vector nonnegative.
   `TauCeti.exists_isSinkAdmissible_vertexPreReflectionList_eq_single` glues those passes into a
   single **sink-admissible** word `w`: repeating a full pass is admissible because reflecting once
   at every vertex restores the quiver (`TauCeti.Quiver.reflectList_eq_self`), and an initial
   segment of an admissible word is admissible.
2. *Read it backwards.* The reverse of a sink-admissible word is source-admissible for the fully
   reflected quiver (`TauCeti.Quiver.IsSinkAdmissible.isSourceAdmissible_reverse`), and
   `TauCeti.nonneg_vertexPreReflectionList_take_reverse` turns the nonnegativity of the forward
   chain into nonnegativity of the backward one: an intermediate vector of the reversed word applied
   to the endpoint `s_w d` *is* one of the forward vectors, because a word and its reverse compose
   to the identity.
3. *Rebuild.* `TauCeti.indecomposable_and_dimVector_sourceReflectionFunctorList` then carries the
   vertex simple `S_j` at the endpoint of the word to an indecomposable representation and realizes
   the reflection product on dimension vectors, which is
   `TauCeti.exists_indecomposable_dimVector_eq_vertexPreReflectionList_single`. Applying the whole
   word gives `s_{w.reverse} (s_w d) = d`.

## Implementation notes

The vector computations are all carried out for the *original* quiver and transferred to the
reflected one at the last moment: the reflection product along a word does not depend on the
orientation (`TauCeti.vertexPreReflectionList_reflectAt`), so no looplessness or Tits-form
hypothesis has to be re-established for a reflected quiver. Arrow-finiteness does have to be
transported, and is, by a private recursion along the word.

As in the neighbouring files the comparison with a vertex simple puts the quiver, its arrows and
the field in one universe: the vertex space of `S_j` is the field itself.

## Main results

* `TauCeti.exists_isSinkAdmissible_vertexPreReflectionList_eq_single`: the Weyl-orbit reduction of a
  positive root, as one sink-admissible word with nonnegative intermediate vectors.
* `TauCeti.nonneg_vertexPreReflectionList_take_reverse`: reading a nonnegative reflection word
  backwards stays nonnegative.
* `TauCeti.exists_indecomposable_dimVector_eq_vertexPreReflectionList_single`: a source-admissible
  word with nonnegative intermediate vectors turns a vertex simple into an indecomposable with the
  reflected dimension vector.
* `TauCeti.exists_indecomposable_dimVector_eq`: **every positive root is the dimension vector of a
  finite-dimensional indecomposable representation**, with
  `TauCeti.titsForm_eq_one_iff_exists_indecomposable` the resulting characterization of the positive
  roots and `TauCeti.exists_indecomposable_dimVector_eq_unique_up_to_iso` the form that adds the
  uniqueness up to isomorphism of the realizing representation.

## References

This is the existence milestone of Layer 5 ("Gabriel's theorem", "Indecomposables are positive
roots") of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2, and Assem--Simson--Skowronski, *Elements of the
Representation Theory of Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

universe u v

/-! ### A single sink-admissible word carrying a positive root to a simple root -/

section Word

variable (Q : Type u) [q : _root_.Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [DecidableEq Q]

/-- Nonnegativity of every intermediate vector along a concatenation follows from nonnegativity
along each of the two segments. -/
private theorem nonneg_vertexPreReflectionList_take_append {d : Q → ℤ} {l₁ l₂ : List Q}
    (h₁ : ∀ r ≤ l₁.length, 0 ≤ vertexPreReflectionList Q (l₁.take r) d)
    (h₂ : ∀ r ≤ l₂.length,
      0 ≤ vertexPreReflectionList Q (l₂.take r) (vertexPreReflectionList Q l₁ d)) :
    ∀ r ≤ (l₁ ++ l₂).length, 0 ≤ vertexPreReflectionList Q ((l₁ ++ l₂).take r) d := by
  intro r hr
  rw [List.take_append, vertexPreReflectionList_append, Module.End.mul_apply]
  rcases le_or_gt r l₁.length with h | h
  · rw [Nat.sub_eq_zero_of_le h, List.take_zero, vertexPreReflectionList_nil,
      Module.End.one_apply]
    exact h₁ r h
  · rw [List.take_of_length_le h.le]
    refine h₂ (r - l₁.length) ?_
    rw [List.length_append] at hr
    omega

/-- Nonnegativity of every intermediate vector along a repeated word follows from nonnegativity
along each of its passes. -/
private theorem nonneg_vertexPreReflectionList_take_flatten_replicate {d : Q → ℤ} (hd : 0 ≤ d)
    {l : List Q} :
    ∀ N : ℕ, (∀ p < N, ∀ r ≤ l.length,
        0 ≤ vertexPreReflectionList Q (l.take r) ((vertexPreReflectionList Q l ^ p) d)) →
      ∀ r ≤ ((List.replicate N l).flatten).length,
        0 ≤ vertexPreReflectionList Q (((List.replicate N l).flatten).take r) d
  | 0, _ => by
      intro r hr
      simp only [List.replicate_zero, List.flatten_nil, List.length_nil, Nat.le_zero] at hr
      subst hr
      simpa using hd
  | N + 1, h => by
      rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      refine nonneg_vertexPreReflectionList_take_append Q
        (nonneg_vertexPreReflectionList_take_flatten_replicate hd N
          fun p hp ↦ h p (by omega)) ?_
      rw [vertexPreReflectionList_flatten_replicate]
      exact h N (by omega)

/-- **The reflection word carrying a positive root to a simple root can be taken
sink-admissible.** For a quiver with positive definite Tits form and a repetition-free
sink-admissible ordering `l` of its vertices, every positive root `d` is carried to a simple root
by a single sink-admissible word, along which no intermediate vector leaves the nonnegative cone.

This packages `TauCeti.exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg`, whose
conclusion is phrased as a number of full passes of `l` followed by an initial segment of it, into
the one word the reflection induction reads backwards. -/
theorem exists_isSinkAdmissible_vertexPreReflectionList_eq_single
    (hpd : (titsForm Q).PosDef) {l : List Q} (hnd : l.Nodup) (hall : ∀ i : Q, i ∈ l)
    (hl : Quiver.IsSinkAdmissible q l) {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ (w : List Q) (j : Q), Quiver.IsSinkAdmissible q w ∧
      vertexPreReflectionList Q w d = Pi.single j 1 ∧
      ∀ r ≤ w.length, 0 ≤ vertexPreReflectionList Q (w.take r) d := by
  obtain ⟨N, m, j, -, heq, hpasses, hlast⟩ :=
    exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg Q hpd hnd hall hd hroot
  -- Repeating a full pass returns the quiver structure, so any number of passes is admissible.
  have hflat : ∀ p : ℕ, Quiver.IsSinkAdmissible q (List.replicate p l).flatten ∧
      Quiver.reflectList q (List.replicate p l).flatten = q := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
        rw [List.replicate_succ, List.flatten_cons]
        refine ⟨Quiver.isSinkAdmissible_append.mpr ⟨hl, ?_⟩, ?_⟩
        · rw [Quiver.reflectList_eq_self q hnd hall]
          exact ih.1
        · rw [Quiver.reflectList_append, Quiver.reflectList_eq_self q hnd hall]
          exact ih.2
  have htake : Quiver.IsSinkAdmissible q (l.take m) :=
    (Quiver.isSinkAdmissible_append.mp
      (by rwa [List.take_append_drop] : Quiver.IsSinkAdmissible q (l.take m ++ l.drop m))).1
  refine ⟨(List.replicate N l).flatten ++ l.take m, j,
    Quiver.isSinkAdmissible_append.mpr ⟨(hflat N).1, ?_⟩, ?_, ?_⟩
  · rw [(hflat N).2]
    exact htake
  · rw [vertexPreReflectionList_append, Module.End.mul_apply,
      vertexPreReflectionList_flatten_replicate]
    exact heq
  · refine nonneg_vertexPreReflectionList_take_append Q
      (nonneg_vertexPreReflectionList_take_flatten_replicate Q hd N hpasses) ?_
    rw [vertexPreReflectionList_flatten_replicate]
    intro r hr
    rw [List.take_take]
    exact hlast _ (min_le_right _ _)

/-- Undoing the reflections of a word in reverse order returns the vector the word started from. -/
private theorem vertexPreReflectionList_reverse_apply_append
    (hloop : ∀ i : Q, IsEmpty (i ⟶ i)) (l₁ l₂ : List Q) (d : Q → ℤ) :
    vertexPreReflectionList Q l₂.reverse (vertexPreReflectionList Q (l₁ ++ l₂) d)
      = vertexPreReflectionList Q l₁ d := by
  rw [vertexPreReflectionList_append, Module.End.mul_apply, ← Module.End.mul_apply,
    vertexPreReflectionList_reverse_mul Q (fun i _ ↦ hloop i), Module.End.one_apply]

/-- **Reading a nonnegative reflection word backwards stays nonnegative.** If every intermediate
vector of the word `w` applied to `d` is nonnegative, then every intermediate vector of the
reversed word applied to the endpoint `sᵂ d` is nonnegative, being one of the vectors of the
forward chain. This is the hypothesis the source-reflection composite of
`TauCeti.indecomposable_and_dimVector_sourceReflectionFunctorList` asks for. -/
theorem nonneg_vertexPreReflectionList_take_reverse (hloop : ∀ i : Q, IsEmpty (i ⟶ i))
    {w : List Q} {d : Q → ℤ} (h : ∀ r ≤ w.length, 0 ≤ vertexPreReflectionList Q (w.take r) d) :
    ∀ s ≤ w.length, 0 ≤ vertexPreReflectionList Q (w.reverse.take s)
      (vertexPreReflectionList Q w d) := by
  intro s hs
  obtain ⟨a, b, rfl, hb⟩ : ∃ a b : List Q, w = a ++ b ∧ b.length = s := by
    refine ⟨w.take (w.length - s), w.drop (w.length - s), (List.take_append_drop _ _).symm, ?_⟩
    rw [List.length_drop]
    omega
  rw [List.reverse_append, ← hb, List.take_left' (by rw [List.length_reverse]),
    vertexPreReflectionList_reverse_apply_append Q hloop]
  have := h a.length (by rw [List.length_append]; omega)
  rwa [List.take_left] at this

end Word

/-! ### Arrow-finiteness along an iterated reflection -/

section Fintype

variable (Q : Type u)

/-- The arrows of an iteratively reflected quiver are finite in number whenever those of the
original one are: reflection only reverses arrows. -/
@[instance_reducible]
private noncomputable def fintypeHomReflectList :
    ∀ (l : List Q) (q₀ : _root_.Quiver.{v} Q)
      (_hq₀ : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b)) (a b : Q),
      Fintype (@_root_.Quiver.Hom Q (Quiver.reflectList q₀ l) a b)
  | [], _, hq₀, a, b => hq₀ a b
  | i :: l, q₀, hq₀, a, b =>
      fintypeHomReflectList l (Quiver.reflectAt q₀ i)
        (@Quiver.instFintypeReflectHom Q q₀ hq₀ i) a b

variable [Fintype Q] [DecidableEq Q]

/-- The reflection product along a word does not depend on the orientation of the quiver, so it is
unchanged by reflecting the quiver along another word. -/
private theorem vertexPreReflectionList_reflectList :
    ∀ (l' : List Q) (q₀ : _root_.Quiver.{v} Q)
      (hq₀ : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b)) (l : List Q),
      @vertexPreReflectionList Q (Quiver.reflectList q₀ l') _
          (fintypeHomReflectList Q l' q₀ hq₀) _ l
        = @vertexPreReflectionList Q q₀ _ hq₀ _ l
  | [], _, _, _ => rfl
  | i :: l', q₀, hq₀, l =>
      (vertexPreReflectionList_reflectList l' (Quiver.reflectAt q₀ i)
          (@Quiver.instFintypeReflectHom Q q₀ hq₀ i) l).trans
        (vertexPreReflectionList_reflectAt Q q₀ hq₀ i l)

end Fintype

/-! ### Rebuilding an indecomposable from a vertex simple -/

section Existence

open CategoryTheory

variable (k Q : Type u) [Field k] [Fintype Q] [DecidableEq Q]

/-- **A nonnegative source-reflection word turns a vertex simple into an indecomposable with the
prescribed dimension vector.** Starting from the vertex simple `Sⱼ` of `q₀` and reflecting along a
source-admissible word `w`, all of whose intermediate dimension vectors stay nonnegative, produces
an indecomposable representation of `TauCeti.Quiver.reflectList q₀ w` whose dimension vector is the
reflection product along `w` of the simple dimension vector `αⱼ`.

This is `TauCeti.indecomposable_and_dimVector_sourceReflectionFunctorList` run at `Sⱼ`, whose
dimension vector `TauCeti.dimVector_simpleRep` identifies as `αⱼ`. -/
theorem exists_indecomposable_dimVector_eq_vertexPreReflectionList_single
    (q₀ : _root_.Quiver.{u} Q) (hq₀ : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b))
    (w : List Q) (j : Q) (hadm : Quiver.IsSourceAdmissible q₀ w)
    (hnn : ∀ r < w.length,
      0 ≤ @vertexPreReflectionList Q q₀ _ hq₀ _ (w.take (r + 1)) (Pi.single j 1)) :
    ∃ M : @QuiverRep.{u, u, u, u} k Q _ (Quiver.reflectList q₀ w),
      Indecomposable M ∧ @IsFinDim.{u, u, u, u} k Q _ (Quiver.reflectList q₀ w) M ∧
        (fun t : Q ↦ (@dimVector k Q _ (Quiver.reflectList q₀ w) M t : ℤ))
          = @vertexPreReflectionList Q q₀ _ hq₀ _ w (Pi.single j 1) := by
  let : _root_.Quiver.{u} Q := q₀
  let : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b) := hq₀
  have hdimsimp : (fun t : Q ↦ (@dimVector k Q _ q₀ (simpleRep k Q j) t : ℤ))
      = Pi.single j 1 := by
    funext t
    rw [dimVector_simpleRep]
    by_cases h : t = j <;> simp [h]
  obtain ⟨hind, hdim⟩ := indecomposable_and_dimVector_sourceReflectionFunctorList.{u, u, u, u}
    w q₀ hq₀ hadm (simpleRep k Q j) (indecomposable_of_simple _)
    (fun a ↦ finiteDimensional_simpleRep_obj j a) (by rw [hdimsimp]; exact hnn)
  refine ⟨_, hind, ?_, ?_⟩
  · exact isFinDim_sourceReflectionFunctorList_obj.{u, u, u, u} w q₀ hq₀ hadm (simpleRep k Q j)
      (isFinDim_iff.mpr fun v ↦ finiteDimensional_simpleRep_obj j v)
  · rw [hdim, hdimsimp]

omit [DecidableEq Q] in
/-- **Every positive root of a quiver with positive definite Tits form is the dimension vector of a
finite-dimensional indecomposable representation.** This is the surjective half of the Gabriel
correspondence; the injective half — that an indecomposable is determined by its dimension vector —
is `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`, and that the dimension
vector of an indecomposable *is* a positive root is
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`.

The representation is built by reading the reflection word of
`TauCeti.exists_isSinkAdmissible_vertexPreReflectionList_eq_single` backwards: the word carries `d`
to a simple root `αⱼ` without leaving the nonnegative cone, so the reversed word is
source-admissible and carries the vertex simple `Sⱼ` back to an indecomposable of dimension
vector `d`. -/
theorem exists_indecomposable_dimVector_eq [q : _root_.Quiver.{u} Q]
    [hq : ∀ a b : Q, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic Q) (hpd : (titsForm Q).PosDef)
    {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ M : QuiverRep.{u, u, u, u} k Q, Indecomposable M ∧ IsFinDim.{u, u, u, u} k Q M ∧
      (fun t : Q ↦ (dimVector M t : ℤ)) = d := by
  classical
  obtain ⟨l, hnd, hall, hl⟩ := hac.exists_isSinkAdmissible
  obtain ⟨w, j, hw, hwd, hnn⟩ :=
    exists_isSinkAdmissible_vertexPreReflectionList_eq_single Q hpd hnd hall hl hd hroot
  have hloop : ∀ i : Q, IsEmpty (i ⟶ i) := isEmpty_hom_self_of_titsForm_posDef Q hpd
  suffices h : ∃ M : @QuiverRep.{u, u, u, u} k Q _
      (Quiver.reflectList (Quiver.reflectList q w) w.reverse),
      Indecomposable M ∧
        @IsFinDim.{u, u, u, u} k Q _
          (Quiver.reflectList (Quiver.reflectList q w) w.reverse) M ∧
        (fun t : Q ↦ (@dimVector k Q _
          (Quiver.reflectList (Quiver.reflectList q w) w.reverse) M t : ℤ)) = d by
    rwa [Quiver.reflectList_reverse_reflectList] at h
  have hnn' : ∀ r < w.reverse.length,
      0 ≤ @vertexPreReflectionList Q (Quiver.reflectList q w) _ (fintypeHomReflectList Q w q hq) _
        (w.reverse.take (r + 1)) (Pi.single j 1) := by
    intro r hr
    rw [vertexPreReflectionList_reflectList Q w q hq, ← hwd]
    exact nonneg_vertexPreReflectionList_take_reverse Q hloop hnn (r + 1)
      (by rw [List.length_reverse] at hr; omega)
  obtain ⟨M, hind, hfd, hdim⟩ :=
    exists_indecomposable_dimVector_eq_vertexPreReflectionList_single k Q
      (Quiver.reflectList q w) (fintypeHomReflectList Q w q hq) w.reverse j
      hw.isSourceAdmissible_reverse hnn'
  refine ⟨M, hind, hfd, ?_⟩
  rw [hdim, vertexPreReflectionList_reflectList Q w q hq, ← hwd, ← Module.End.mul_apply,
    vertexPreReflectionList_reverse_mul Q fun i _ ↦ hloop i, Module.End.one_apply]

omit [DecidableEq Q] in
/-- **A nonnegative vector is a positive root exactly when it is realized by an indecomposable
representation.** The forward direction is `TauCeti.exists_indecomposable_dimVector_eq`; the reverse
is `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`, which needs no nonnegativity
hypothesis, a dimension vector being nonnegative of itself. -/
theorem titsForm_eq_one_iff_exists_indecomposable [q : _root_.Quiver.{u} Q]
    [hq : ∀ a b : Q, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic Q) (hpd : (titsForm Q).PosDef)
    {d : Q → ℤ} (hd : 0 ≤ d) :
    titsForm Q d = 1 ↔ ∃ M : QuiverRep.{u, u, u, u} k Q, Indecomposable M ∧
      IsFinDim.{u, u, u, u} k Q M ∧ (fun t : Q ↦ (dimVector M t : ℤ)) = d := by
  refine ⟨fun hroot ↦ exists_indecomposable_dimVector_eq k Q hac hpd hd hroot, ?_⟩
  rintro ⟨M, hM, hfd, rfl⟩
  exact titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic hac hpd M hM hfd

omit [DecidableEq Q] in
/-- **Gabriel's correspondence at a positive root**: a positive root of a positive definite Tits
form is the dimension vector of a finite-dimensional indecomposable representation, and that
representation is unique up to isomorphism. The existence half is
`TauCeti.exists_indecomposable_dimVector_eq` and the uniqueness half is
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`; together they say that
`M ↦ dim M` is a bijection from the isomorphism classes of finite-dimensional indecomposables onto
the positive roots. -/
theorem exists_indecomposable_dimVector_eq_unique_up_to_iso [q : _root_.Quiver.{u} Q]
    [hq : ∀ a b : Q, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic Q) (hpd : (titsForm Q).PosDef)
    {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ M : QuiverRep.{u, u, u, u} k Q, Indecomposable M ∧ IsFinDim.{u, u, u, u} k Q M ∧
      (fun t : Q ↦ (dimVector M t : ℤ)) = d ∧
      ∀ N : QuiverRep.{u, u, u, u} k Q, Indecomposable N → IsFinDim.{u, u, u, u} k Q N →
        (fun t : Q ↦ (dimVector N t : ℤ)) = d → Nonempty (M ≅ N) := by
  obtain ⟨M, hM, hfdM, hdM⟩ := exists_indecomposable_dimVector_eq k Q hac hpd hd hroot
  refine ⟨M, hM, hfdM, hdM, fun N hN hfdN hdN ↦ ?_⟩
  refine nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic hac hpd M N hM hN hfdM hfdN ?_
  exact funext fun t ↦ Nat.cast_inj.mp (congrFun (hdM.trans hdN.symm) t)

end Existence

end TauCeti
