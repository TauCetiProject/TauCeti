/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table

/-!
# Interior deductions in a coset table

A closed word can determine an interior edge when all edges before and after it are sound.
The prefix acts injectively because the acting monoid is a group. The named points need not
be distinct, and the table itself need not define a group action.
-/

public section

namespace TauCeti.CosetTable

variable {m k : ℕ} {T : CosetTable m k}

private theorem prod_smul_point_of_edges {G α : Type*} [Monoid G] [MulAction G α]
    {g : Fin m → G} {a : α} (i : Fin k) :
    ∀ u : List (Fin m),
      (∀ e ∈ T.edges u i,
        g e.1 • T.point g a e.2 = T.point g a (T.act e.1 e.2)) →
      (u.map g).prod • T.point g a i = T.point g a (T.trace u i)
  | [], _ => by simp
  | t :: u, hu => by
    have hu' := fun e he ↦ hu e (List.mem_cons_of_mem (t, T.trace u i) he)
    rw [List.map_cons, List.prod_cons, mul_smul,
      prod_smul_point_of_edges i u hu', trace_cons]
    exact hu _ List.mem_cons_self

/-- A closed word `pre ++ t :: post` determines its interior edge when the suffix and prefix
edges are sound and its table trace closes. Closedness is required at the starting named point;
no injectivity of the named points or faithfulness of the group action is required. -/
theorem smul_point_of_closed_split {G α : Type*} [Group G] [MulAction G α]
    {g : Fin m → G} {a : α} {pre post : List (Fin m)} {t : Fin m} {i : Fin k}
    (hr : ((pre ++ t :: post).map g).prod • T.point g a i = T.point g a i)
    (hpost : ∀ e ∈ T.edges post i,
      g e.1 • T.point g a e.2 = T.point g a (T.act e.1 e.2))
    (hpre : ∀ e ∈ T.edges pre (T.act t (T.trace post i)),
      g e.1 • T.point g a e.2 = T.point g a (T.act e.1 e.2))
    (hclose : T.trace pre (T.act t (T.trace post i)) = i) :
    g t • T.point g a (T.trace post i) = T.point g a (T.act t (T.trace post i)) := by
  have hpost' := prod_smul_point_of_edges i post hpost
  have hpre' := prod_smul_point_of_edges (T.act t (T.trace post i)) pre hpre
  rw [hclose] at hpre'
  rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    mul_smul, mul_smul, hpost'] at hr
  exact MulAction.injective ((pre.map g).prod) (hr.trans hpre'.symm)

end TauCeti.CosetTable
