/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.TitsForm
public import TauCeti.RepresentationTheory.Quiver.Reflection.PositiveRoot
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Composite
public import TauCeti.RepresentationTheory.Quiver.Reflection.Uniqueness

/-!
# Every positive root is the dimension vector of an indecomposable representation

Let `Q` be a finite quiver whose Tits form is positive definite, the numerical side of the ADE
condition in Gabriel's theorem. `TauCeti.titsForm_dimVector_eq_one_of_indecomposable` sends a
finite-dimensional indecomposable representation of `Q` to a positive root of the Tits form, and
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable` shows that map injective on isomorphism
classes. This file proves it **surjective**: every positive root is realized
(`TauCeti.exists_indecomposable_dimVector_eq`), so `M ↦ dim M` is a bijection from the isomorphism
classes of finite-dimensional indecomposables onto the positive roots. No algebraic closedness is
needed anywhere: the Bernstein-Gelfand-Ponomarev reflection functors work over any field.

Where the injective half runs the sink reflection functors forwards until they annihilate the
representation, the surjective half runs the *source* reflection functors backwards from a vertex
simple. `TauCeti.exists_isSinkAdmissible_vertexPreReflectionList_eq_single_and_nonneg` supplies
the word to travel along,
`TauCeti.exists_indecomposable_dimVector_eq_vertexPreReflectionList_single` travels along its
reverse, and `TauCeti.exists_indecomposable_dimVector_eq` is their composite.

## Implementation notes

The vector computations are all carried out for the *original* quiver and transferred to the
reflected one at the last moment: the reflection product along a word does not depend on the
orientation (`TauCeti.vertexPreReflectionList_reflectList`), so no looplessness or Tits-form
hypothesis has to be re-established for a reflected quiver. Arrow-finiteness is transported by
`TauCeti.Quiver.fintypeHomReflectList`.

As in the neighbouring files, the universe of the vertex spaces is chosen large enough for the
vertices, arrows, and field. The construction therefore starts from a universe lift of `Sⱼ`,
whose nonzero vertex space remains a one-dimensional copy of the field.

## Main results

* `TauCeti.exists_isSinkAdmissible_vertexPreReflectionList_eq_single_and_nonneg`: the Weyl-orbit
  reduction of a positive root, as one sink-admissible word with nonnegative intermediate vectors.
* `TauCeti.exists_indecomposable_dimVector_eq_vertexPreReflectionList_single`: a source-admissible
  word with nonnegative intermediate vectors turns a vertex simple into an indecomposable with the
  reflected dimension vector.
* `TauCeti.exists_indecomposable_dimVector_eq`: **every positive root is the dimension vector of a
  finite-dimensional indecomposable representation**, with
  `TauCeti.nonneg_and_titsForm_eq_one_iff_exists_indecomposable` the resulting characterization of
  the positive roots.

## References

Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2, and Assem--Simson--Skowronski, *Elements of the
Representation Theory of Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

universe u v w x

-- The argument, step by step:
-- 1. One word. `exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg` carries a positive
--    root `d` to a simple root by finitely many full passes of a sink-admissible ordering followed
--    by an initial segment of it, with every intermediate vector nonnegative;
--    `exists_isSinkAdmissible_vertexPreReflectionList_eq_single_and_nonneg` glues those passes into
--    one sink-admissible word.
-- 2. Read it backwards. The reverse of a sink-admissible word is source-admissible for the fully
--    reflected quiver (`Quiver.IsSinkAdmissible.isSourceAdmissible_reverse`), and
--    `nonneg_vertexPreReflectionList_take_reverse` turns the nonnegativity of the forward chain
--    into nonnegativity of the backward one.
-- 3. Rebuild. `indecomposable_and_dimVector_sourceReflectionFunctorList` carries the vertex simple
--    `Sⱼ` at the endpoint of the word back to an indecomposable representation, which is
--    `exists_indecomposable_dimVector_eq_vertexPreReflectionList_single`.

/-! ### A single sink-admissible word carrying a positive root to a simple root -/

section Word

variable (Q : Type v) [q : _root_.Quiver.{w} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [DecidableEq Q]

/-- **The reflection word carrying a positive root to a simple root can be taken
sink-admissible.** For a quiver with positive definite Tits form, every positive root `d` is carried
to a simple root by a single sink-admissible word, along which no intermediate vector leaves the
nonnegative cone.

This is `TauCeti.exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg`, whose conclusion
is phrased as a number of full passes of a sink-admissible ordering followed by an initial segment
of it, restated as the one word the reflection induction reads backwards. -/
theorem exists_isSinkAdmissible_vertexPreReflectionList_eq_single_and_nonneg
    (hpd : (titsForm Q).PosDef) {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ (l : List Q) (j : Q), Quiver.IsSinkAdmissible q l ∧
      vertexPreReflectionList Q l d = Pi.single j 1 ∧
      ∀ r ≤ l.length, 0 ≤ vertexPreReflectionList Q (l.take r) d := by
  obtain ⟨l, hnd, hall, hl⟩ :=
    (isAcyclic_of_titsForm_posDef hpd).exists_isSinkAdmissible
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

end Word

/-! ### Rebuilding an indecomposable from a vertex simple -/

section Existence

open CategoryTheory

variable (k : Type u) (Q : Type v) [Field k] [Fintype Q] [DecidableEq Q]

/-- **A nonnegative source-reflection word turns a vertex simple into an indecomposable with the
prescribed dimension vector.** Starting from the vertex simple `Sⱼ` of `q₀` and reflecting along a
source-admissible word `l`, all of whose intermediate dimension vectors stay nonnegative, produces
an indecomposable representation of `TauCeti.Quiver.reflectList q₀ l` whose dimension vector is the
reflection product along `l` of the simple dimension vector `αⱼ`. -/
theorem exists_indecomposable_dimVector_eq_vertexPreReflectionList_single
    (q₀ : _root_.Quiver.{w} Q) (hq₀ : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b))
    (l : List Q) (j : Q) (hadm : Quiver.IsSourceAdmissible q₀ l)
    (hnn : ∀ r < l.length,
      0 ≤ @vertexPreReflectionList Q q₀ _ hq₀ _ (l.take (r + 1)) (Pi.single j 1)) :
    ∃ M : @QuiverRep.{u, v, w, max u v w x} k Q _ (Quiver.reflectList q₀ l),
      Indecomposable M ∧
        @IsFinDim.{u, v, w, max u v w x} k Q _ (Quiver.reflectList q₀ l) M ∧
        (fun t : Q ↦ (@dimVector k Q _ (Quiver.reflectList q₀ l) M t : ℤ))
          = @vertexPreReflectionList Q q₀ _ hq₀ _ l (Pi.single j 1) := by
  let : _root_.Quiver.{w} Q := q₀
  let : ∀ a b : Q, Fintype (@_root_.Quiver.Hom Q q₀ a b) := hq₀
  let S : @QuiverRep.{u, v, w, max u v w x} k Q _ q₀ :=
    simpleRep k Q j ⋙ ModuleCat.uliftFunctor.{max v w x, u} k
  -- The dimension vector of the vertex simple is the simple root the word starts from.
  have hdimsimp : (fun t : Q ↦ (@dimVector k Q _ q₀ S t : ℤ)) = Pi.single j 1 := by
    funext t
    rw [dimVector_apply]
    -- `uliftFunctor` has no object rewrite lemma; expose its carrier to apply `finrank_ulift`.
    change (Module.finrank k
      (ULift.{max v w x, u} ((simpleRep k Q j).obj ((Paths.of Q).obj t))) : ℤ) = _
    rw [finrank_ulift]
    have ht := congrFun (dimVector_simpleRep (k := k) (Q := Q) j) t
    rw [dimVector_apply] at ht
    calc
      (Module.finrank k ((simpleRep k Q j).obj ((Paths.of Q).obj t)) : ℤ) =
          ((Pi.single j (1 : ℕ) : Q → ℕ) t : ℤ) := congrArg Int.ofNat ht
      _ = (Pi.single j (1 : ℤ) : Q → ℤ) t := by
        by_cases h : t = j <;> simp [h]
  have hS : Indecomposable S := by
    let _ : Simple S := simple_simpleRep_comp_uliftFunctor.{u, v, w, x} k Q j
    exact indecomposable_of_simple S
  have hfdS : ∀ a : Q, FiniteDimensional k (S.obj a) := by
    intro a
    exact ULift.moduleEquiv.symm.finiteDimensional
  obtain ⟨hind, hdim⟩ :=
    indecomposable_and_dimVector_sourceReflectionFunctorList.{u, v, w, max u x}
      l q₀ hq₀ hadm S hS hfdS (by rw [hdimsimp]; exact hnn)
  refine ⟨_, hind, ?_, ?_⟩
  · exact isFinDim_sourceReflectionFunctorList_obj.{u, v, w, max u x}
      l q₀ hq₀ hadm S (isFinDim_iff.mpr hfdS)
  · rw [hdim, hdimsimp]

omit [DecidableEq Q] in
/-- **Every positive root of a quiver with positive definite Tits form is the dimension vector of a
finite-dimensional indecomposable representation.** This is the surjective half of the Gabriel
correspondence; the injective half — that an indecomposable is determined by its dimension vector —
is `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`, and that the dimension
vector of an indecomposable *is* a positive root is
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`. -/
theorem exists_indecomposable_dimVector_eq [q : _root_.Quiver.{w} Q]
    [hq : ∀ a b : Q, Fintype (a ⟶ b)] (hpd : (titsForm Q).PosDef)
    {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ M : QuiverRep.{u, v, w, max u v w x} k Q, Indecomposable M ∧
      IsFinDim.{u, v, w, max u v w x} k Q M ∧
      (fun t : Q ↦ (dimVector M t : ℤ)) = d := by
  classical
  -- A sink-admissible word carries `d` to a simple root without leaving the nonnegative cone, so
  -- the reversed word is source-admissible and carries the vertex simple `Sⱼ` back to `d`.
  obtain ⟨l, j, hl, hld, hnn⟩ :=
    exists_isSinkAdmissible_vertexPreReflectionList_eq_single_and_nonneg Q hpd hd hroot
  have hloop : ∀ i : Q, IsEmpty (i ⟶ i) := isEmpty_hom_self_of_titsForm_posDef Q hpd
  suffices h : ∃ M : @QuiverRep.{u, v, w, max u v w x} k Q _
      (Quiver.reflectList (Quiver.reflectList q l) l.reverse),
      Indecomposable M ∧
        @IsFinDim.{u, v, w, max u v w x} k Q _
          (Quiver.reflectList (Quiver.reflectList q l) l.reverse) M ∧
        (fun t : Q ↦ (@dimVector k Q _
          (Quiver.reflectList (Quiver.reflectList q l) l.reverse) M t : ℤ)) = d by
    rwa [Quiver.reflectList_reverse_reflectList] at h
  have hnn' : ∀ r < l.reverse.length,
      0 ≤ @vertexPreReflectionList Q (Quiver.reflectList q l) _
        (Quiver.fintypeHomReflectList l q hq) _ (l.reverse.take (r + 1)) (Pi.single j 1) := by
    intro r hr
    rw [vertexPreReflectionList_reflectList Q l q hq, ← hld]
    exact nonneg_vertexPreReflectionList_take_reverse Q (fun i _ ↦ hloop i) hnn (r + 1)
      (by rw [List.length_reverse] at hr; omega)
  obtain ⟨M, hind, hfd, hdim⟩ :=
    exists_indecomposable_dimVector_eq_vertexPreReflectionList_single.{u, v, w, x} k Q
      (Quiver.reflectList q l) (Quiver.fintypeHomReflectList l q hq) l.reverse j
      hl.isSourceAdmissible_reverse hnn'
  refine ⟨M, hind, hfd, ?_⟩
  rw [hdim, vertexPreReflectionList_reflectList Q l q hq, ← hld, ← Module.End.mul_apply,
    vertexPreReflectionList_reverse_mul Q fun i _ ↦ hloop i, Module.End.one_apply]

omit [DecidableEq Q] in
/-- **A vector is a nonnegative root exactly when it is realized by an indecomposable
representation.** The forward direction is `TauCeti.exists_indecomposable_dimVector_eq`; the reverse
is `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`, nonnegativity being automatic
for a dimension vector. -/
theorem nonneg_and_titsForm_eq_one_iff_exists_indecomposable [q : _root_.Quiver.{w} Q]
    [hq : ∀ a b : Q, Fintype (a ⟶ b)] (hpd : (titsForm Q).PosDef) {d : Q → ℤ} :
    0 ≤ d ∧ titsForm Q d = 1 ↔ ∃ M : QuiverRep.{u, v, w, max u v w x} k Q,
      Indecomposable M ∧ IsFinDim.{u, v, w, max u v w x} k Q M ∧
        (fun t : Q ↦ (dimVector M t : ℤ)) = d := by
  refine ⟨fun ⟨hd, hroot⟩ ↦
    exists_indecomposable_dimVector_eq.{u, v, w, x} k Q hpd hd hroot, ?_⟩
  rintro ⟨M, hM, hfd, rfl⟩
  exact ⟨fun t ↦ Int.natCast_nonneg _,
    titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic.{u, v, w, max u x}
      (isAcyclic_of_titsForm_posDef hpd) hpd M hM hfd⟩

end Existence

end TauCeti
