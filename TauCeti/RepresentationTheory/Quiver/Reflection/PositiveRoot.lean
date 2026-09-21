/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Descent

/-!
# Every positive root of a positive definite Tits form is a reflection of a simple root

Let `Q` be a finite quiver whose Tits form is positive definite. A **positive root** is a nonzero
`d : Q → ℤ` with `0 ≤ d` and `titsForm Q d = 1`; the dimension vector of a finite-dimensional
indecomposable representation is one, by
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable`. This file proves the root-lattice statement
that every positive root is carried to a **simple** root `αⱼ = Pi.single j 1` by finitely many
simple reflections read along a repetition-free word running over all the vertices. Equivalently,
every positive root lies in the Weyl orbit of a simple one.

This is a prerequisite for the reflection induction in Gabriel's theorem. The reduction records
that every intermediate vector remains nonnegative, so the reverse word can be transported through
source reflection functors. It does not assert that the reflection word is sink- or
source-admissible for the evolving quivers; that property comes from choosing the full word to be a
sink-admissible ordering.

## Main results

* `TauCeti.vertexPreReflection_apply_self_neg_iff_eq_single`: **a positive root is simple exactly
  when the reflection at that vertex makes its coordinate there negative.**
* `TauCeti.exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg`: some number of full
  passes of the reflection product followed by an initial segment of the word carries a positive
  root to the simple root at the next vertex of the word, without leaving the nonnegative cone
  before reaching that root.
* `TauCeti.titsForm_eq_one_iff_exists_vertexPreReflectionList_single`: consequently the positive
  roots are exactly the nonnegative reflection images of the simple roots.

## References

Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q]

/-! ### One reflection detects the simple roots -/

/-- **A single reflection turns a positive root negative exactly at a simple root.** For a
positive definite Tits form and a nonnegative `d` with `q(d) = 1`, the coordinate of `sᵢ d` at `i`
is negative precisely when `d` is the simple dimension vector `αᵢ`.

Thus a positive root can leave the positive cone under a simple reflection only when it is the
corresponding simple root. -/
@[simp]
theorem vertexPreReflection_apply_self_neg_iff_eq_single (hpd : (titsForm Q).PosDef) {i : Q}
    {d : Q → ℤ} (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    vertexPreReflection Q i d i < 0 ↔ d = Pi.single i 1 := by
  have hloop : IsEmpty (i ⟶ i) := isEmpty_hom_self_of_titsForm_posDef Q hpd i
  constructor
  · intro hneg
    set S : ℤ := ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v
      with hSdef
    have hS0 : 0 ≤ S :=
      Finset.sum_nonneg fun v _ ↦
        mul_nonneg (add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
          (by simpa using Pi.le_def.mp hd v)
    have hSa : S < d i := by
      have hself := vertexPreReflection_apply_self Q i d
      rw [← hSdef] at hself
      rw [hself] at hneg
      linarith
    -- split `d` into its `i`-th coordinate and the rest
    set r : Q → ℤ := d - d i • (Pi.single i 1 : Q → ℤ) with hrdef
    have hri : r i = 0 := by simp [hrdef]
    have hdr : d = r + d i • (Pi.single i 1 : Q → ℤ) := by rw [hrdef]; abel
    have hSr : ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * r v = S := by
      rw [hSdef]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rcases eq_or_ne v i with rfl | hv
      · rw [hri, Fintype.card_eq_zero_iff.mpr hloop]
        simp
      · rw [hrdef]
        simp [hv]
    -- the Tits form of `d`, expanded along that splitting
    have hpolar : titsPolarForm Q r (Pi.single i 1) = -S := by
      rw [titsPolarForm_comm, titsPolarForm_single_left, hri, hSr]
      ring
    have hexpand : titsForm Q d = titsForm Q r + d i * d i + d i * -S := by
      conv_lhs => rw [hdr]
      rw [titsForm_add, QuadraticMap.map_smul, titsForm_single_of_isEmpty Q hloop, map_smul,
        hpolar, smul_eq_mul, smul_eq_mul, mul_one]
    have hkey : titsForm Q r + d i * (d i - S) = 1 := by rw [← hroot, hexpand]; ring
    -- positive definiteness pins both summands
    have hrnn : 0 ≤ titsForm Q r := hpd.nonneg r
    have hprod : 1 ≤ d i * (d i - S) := by nlinarith
    have hr0 : titsForm Q r = 0 := by linarith
    have hprod1 : d i * (d i - S) = 1 := by linarith
    have hale : d i ≤ 1 := by
      have hmul : d i * 1 ≤ d i * (d i - S) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rwa [mul_one, hprod1] at hmul
    have ha1 : d i = 1 := le_antisymm hale (by linarith)
    rw [hdr, hpd.anisotropic r hr0, ha1, one_smul, zero_add]
  · rintro rfl
    rw [vertexPreReflection_single_self Q hloop]
    simp

/-! ### Reduction of a positive root to a simple root -/

/-- **Weyl-orbit reduction with nonnegative intermediate vectors.** For a quiver with positive
definite Tits form and a repetition-free word `l` running over all the vertices, every positive
root `d` is carried to a simple root by finitely many full passes of the reflection product
followed by an initial segment of `l`: the simple root is the one at the vertex `l` reaches next.

Every intermediate vector in each earlier pass, and every intermediate vector up to the returned
initial segment in the final pass, is nonnegative. This is the condition needed to reverse the word
using source reflection functors: none of the intermediate vectors asks for a representation with a
negative vertex dimension.

No admissibility property of the word for successive reflected quivers is asserted. Reading the
word backwards exhibits `d` in the Weyl orbit of a simple root, as recorded by
`TauCeti.titsForm_eq_one_iff_exists_vertexPreReflectionList_single`. -/
theorem exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg (hpd : (titsForm Q).PosDef)
    {l : List Q} (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l) {d : Q → ℤ}
    (hd : 0 ≤ d) (hroot : titsForm Q d = 1) :
    ∃ (N m : ℕ) (j : Q), l[m]? = some j ∧
      vertexPreReflectionList Q (l.take m) ((vertexPreReflectionList Q l ^ N) d)
        = Pi.single j 1 ∧
      (∀ p < N, ∀ r ≤ l.length,
        0 ≤ vertexPreReflectionList Q (l.take r) ((vertexPreReflectionList Q l ^ p) d)) ∧
      ∀ r ≤ m,
        0 ≤ vertexPreReflectionList Q (l.take r) ((vertexPreReflectionList Q l ^ N) d) := by
  classical
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hroot
    exact zero_ne_one hroot
  have hloop : ∀ j : Q, IsEmpty (j ⟶ j) := isEmpty_hom_self_of_titsForm_posDef Q hpd
  have hword : ∀ (w : List Q) (y : Q → ℤ),
      titsForm Q (vertexPreReflectionList Q w y) = titsForm Q y :=
    fun w y ↦ titsForm_vertexPreReflectionList Q (fun j _ ↦ hloop j) y
  have hpow : ∀ N : ℕ, titsForm Q ((vertexPreReflectionList Q l ^ N) d) = 1 := by
    intro N
    induction N with
    | zero => simpa using hroot
    | succ N ih => rw [pow_succ', Module.End.mul_apply, hword, ih]
  -- Choose the first pass containing a reflection that leaves the positive cone. Such a pass
  -- exists because a negative coordinate after a full pass is witnessed by its full prefix.
  have hbad : ∃ N m : ℕ, ∃ j : Q,
      vertexPreReflectionList Q (l.take m) ((vertexPreReflectionList Q l ^ N) d) j < 0 := by
    obtain ⟨n, j, hj⟩ := exists_vertexPreReflectionList_pow_apply_neg Q hpd hnd hmem hd0
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Module.End.one_apply] at hj
      exact absurd hj (not_lt.mpr (Pi.le_def.mp hd j))
    obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨N, l.length, j, ?_⟩
    simpa [pow_succ', Module.End.mul_apply] using hj
  let IsBadPass : ℕ → Prop := fun N ↦ ∃ m : ℕ, ∃ j : Q,
    vertexPreReflectionList Q (l.take m) ((vertexPreReflectionList Q l ^ N) d) j < 0
  have hbadPass : ∃ N, IsBadPass N := by
    obtain ⟨N, m, j, h⟩ := hbad
    exact ⟨N, m, j, h⟩
  let N := Nat.find hbadPass
  have hNneg : ∃ m : ℕ, ∃ j : Q,
      vertexPreReflectionList Q (l.take m) ((vertexPreReflectionList Q l ^ N) d) j < 0 :=
    Nat.find_spec hbadPass
  have hNmin : ∀ p < N, ¬ IsBadPass p := fun p hp ↦ Nat.find_min hbadPass hp
  have hpasses : ∀ p < N, ∀ r : ℕ,
      0 ≤ vertexPreReflectionList Q (l.take r) ((vertexPreReflectionList Q l ^ p) d) := by
    intro p hp r
    exact Pi.le_def.mpr fun j ↦ not_lt.mp fun h ↦ hNmin p hp ⟨r, j, h⟩
  -- The vector at the start of the first bad pass is still nonnegative.
  set x : Q → ℤ := (vertexPreReflectionList Q l ^ N) d with hxdef
  have hx : 0 ≤ x := by
    rcases N with _ | N
    · simpa [x] using hd
    · have h := hpasses N (Nat.lt_succ_self N) l.length
      simpa [x, pow_succ', Module.End.mul_apply] using h
  have hxroot : titsForm Q x = 1 := hpow N
  -- Inside that pass, choose the first bad prefix.
  let m := Nat.find hNneg
  have hmneg : ∃ j : Q, vertexPreReflectionList Q (l.take m) x j < 0 :=
    Nat.find_spec hNneg
  have hmmin : ∀ r < m, ∀ j : Q, 0 ≤ vertexPreReflectionList Q (l.take r) x j := by
    intro r hr j
    exact not_lt.mp fun h ↦ Nat.find_min hNneg hr ⟨j, h⟩
  have hm0 : m ≠ 0 := by
    intro hm
    obtain ⟨j, hj⟩ := hmneg
    rw [hm] at hj
    simp only [List.take_zero, vertexPreReflectionList_nil, Module.End.one_apply] at hj
    exact absurd hj (not_lt.mpr (Pi.le_def.mp hx j))
  obtain ⟨k, hmk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hk : 0 ≤ vertexPreReflectionList Q (l.take k) x :=
    Pi.le_def.mpr fun j ↦ hmmin k (by omega) j
  have hklen : k < l.length := by
    by_contra hcon
    obtain ⟨j, hj⟩ := hmneg
    have htake : l.take m = l.take k := by
      rw [(List.take_eq_self_iff l).mpr (by omega), (List.take_eq_self_iff l).mpr (by omega)]
    rw [htake] at hj
    exact absurd hj (not_lt.mpr (hmmin k (by omega) j))
  -- the offending reflection is the one at `l[k]`
  refine ⟨N, k, l[k], List.getElem?_eq_getElem hklen, ?_, ?_, ?_⟩
  · have hstep : vertexPreReflectionList Q (l.take (k + 1)) x
        = vertexPreReflection Q l[k] (vertexPreReflectionList Q (l.take k) x) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hklen, vertexPreReflectionList_append]
      simp [Module.End.mul_apply]
    obtain ⟨w, hw⟩ := hmneg
    rw [hmk] at hw
    rw [hstep] at hw
    have hwk : w = l[k] := by
      by_contra hne
      rw [vertexPreReflection_apply_of_ne Q _ _ hne] at hw
      exact absurd hw (not_lt.mpr (by simpa using Pi.le_def.mp hk w))
    subst hwk
    refine (vertexPreReflection_apply_self_neg_iff_eq_single Q hpd hk ?_).mp hw
    rw [hword, hxroot]
  · exact fun p hp r _ ↦ hpasses p hp r
  · exact fun r hr ↦ Pi.le_def.mpr fun j ↦ hmmin r (by omega) j

/-- **The positive roots are exactly the nonnegative reflection images of the simple roots.** For a
quiver with positive definite Tits form, a nonnegative dimension vector has Tits norm one if and
only if it is obtained from a simple dimension vector by a product of simple reflections.

Combined with `TauCeti.titsForm_dimVector_eq_one_of_indecomposable`, this places the dimension
vector of every finite-dimensional indecomposable representation in the Weyl orbit of a simple
dimension vector. -/
theorem titsForm_eq_one_iff_exists_vertexPreReflectionList_single (hpd : (titsForm Q).PosDef)
    {d : Q → ℤ} (hd : 0 ≤ d) :
    titsForm Q d = 1 ↔
      ∃ (w : List Q) (j : Q), vertexPreReflectionList Q w (Pi.single j 1) = d := by
  classical
  let l : List Q := Finset.univ.toList
  have hnd : l.Nodup := by exact Finset.nodup_toList _
  have hmem : ∀ i : Q, i ∈ l := by
    intro i
    exact Finset.mem_toList.mpr (Finset.mem_univ i)
  have hloop : ∀ j : Q, IsEmpty (j ⟶ j) := isEmpty_hom_self_of_titsForm_posDef Q hpd
  constructor
  · intro hroot
    obtain ⟨N, m, j, -, hEq, -, -⟩ :=
      exists_vertexPreReflectionList_take_apply_eq_single_and_nonneg Q hpd hnd hmem hd hroot
    refine ⟨((List.replicate N l).flatten ++ l.take m).reverse, j, ?_⟩
    have hfwd : vertexPreReflectionList Q ((List.replicate N l).flatten ++ l.take m) d
        = Pi.single j 1 := by
      rw [vertexPreReflectionList_append, Module.End.mul_apply,
        vertexPreReflectionList_flatten_replicate]
      exact hEq
    rw [← hfwd, ← Module.End.mul_apply,
      vertexPreReflectionList_reverse_mul Q (fun i _ ↦ hloop i), Module.End.one_apply]
  · rintro ⟨w, j, rfl⟩
    rw [titsForm_vertexPreReflectionList Q (fun i _ ↦ hloop i),
      titsForm_single_of_isEmpty Q (hloop j)]

end TauCeti
