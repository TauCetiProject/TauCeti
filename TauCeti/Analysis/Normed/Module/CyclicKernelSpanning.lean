/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ShortGenerators
import TauCeti.LinearAlgebra.End.CyclicNorm

/-!
# Short generators of simultaneous cyclic norm kernels

For a list of commuting operators of invertible periods, short integral generators of the
ambient module give short integral generators of the common cyclic norm kernel. The squared
size bound increases by at most a factor of four per operator. In the application to right
translations the size bounds are pointwise on the values of a form, with no invariance
assumption on the individual evaluations.

This is the passage from short source forms to short ramified forms in
`New.Data.span_isShort_ramifiedSourceForms_eq_top` of lsernau/grh-lean at `72fead1`,
`grh/src/New/UpperBound/Size/ShortColumns.lean`.
-/

public section

open Set

namespace List

/-- Short integral vectors span the common kernel of the cyclic norms, with a squared size
budget of `4 ^ s.length * B` when the ambient module has short integral generators at budget
`B`. The operators may move the seminorms within the observing family. -/
theorem span_short_eq_iInf_ker_geom_sum {R V ι A : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (s : List ι) (T : ι → Module.End R V) (n : ι → ℕ)
    (hcomm : s.Pairwise fun i j ↦ Commute (T i) (T j))
    (hn : ∀ i ∈ s, IsUnit (n i : R)) (hT : ∀ i ∈ s, T i ^ n i = 1)
    {L : AddSubgroup V} {p : A → AddGroupSeminorm V} (hL : ∀ i ∈ s, MapsTo (T i) L L)
    (hp : ∀ i ∈ s, ∀ x ∈ L, ∀ a, ∃ b, p a (T i x) ≤ p b x)
    {B : ℝ} (hspan : Submodule.span R {x | x ∈ L ∧ ∀ a, (p a x) ^ 2 ≤ B} = ⊤) :
    let K := ⨅ i ∈ s, LinearMap.ker (∑ j ∈ Finset.range (n i), T i ^ j)
    Submodule.span R {x | x ∈ K ∧ x ∈ L ∧ ∀ a, (p a x) ^ 2 ≤ 4 ^ s.length * B} = K := by
  dsimp only
  rw [← s.range_map_prod_one_sub_eq_iInf_ker_geom_sum T n hcomm hn hT]
  simpa only [List.length_map, List.map_map, Function.comp_def] using
    TauCeti.span_short_list_prod_one_sub_eq_range (l := s.map T) (p := p)
      (fun _ hu ↦ by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu; exact hL i hi)
      (fun _ hu ↦ by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu; exact hp i hi) hspan

/-- For operators acting by reindexing evaluations (such as right translations), the common
cyclic norm kernel is spanned by integral forms whose pointwise squared size bounds increase
by at most `4 ^ s.length`. The additive seminorms on values can include observations after
field conjugation. -/
theorem span_short_eval_eq_iInf_ker_geom_sum {R V W G ι A : Type*} [Ring R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] (s : List ι) (T : ι → Module.End R V) (n : ι → ℕ)
    (hcomm : s.Pairwise fun i j ↦ Commute (T i) (T j))
    (hn : ∀ i ∈ s, IsUnit (n i : R)) (hT : ∀ i ∈ s, T i ^ n i = 1)
    {L : AddSubgroup V} (hL : ∀ i ∈ s, MapsTo (T i) L L)
    (ev : G → V →+ W) (shift : ι → G → G)
    (heval : ∀ i ∈ s, ∀ x ∈ L, ∀ g, ev g (T i x) = ev (shift i g) x)
    (p : A → AddGroupSeminorm W) {B : ℝ}
    (hspan : Submodule.span R {x | x ∈ L ∧ ∀ a g, (p a (ev g x)) ^ 2 ≤ B} = ⊤) :
    let K := ⨅ i ∈ s, LinearMap.ker (∑ j ∈ Finset.range (n i), T i ^ j)
    Submodule.span R {x | x ∈ K ∧ x ∈ L ∧ ∀ a g, (p a (ev g x)) ^ 2 ≤ 4 ^ s.length * B} = K := by
  let q (ag : A × G) : AddGroupSeminorm V := (p ag.1).comp (ev ag.2)
  have hq (i : ι) (hi : i ∈ s) (x : V) (hx : x ∈ L) (ag : A × G) :
      ∃ bg, q ag (T i x) ≤ q bg x := by
    refine ⟨(ag.1, shift i ag.2), ?_⟩
    simp only [q, AddGroupSeminorm.comp_apply, heval i hi x hx, le_refl]
  simpa only [q, AddGroupSeminorm.comp_apply, Prod.forall] using
    s.span_short_eq_iInf_ker_geom_sum T n hcomm hn hT hL hq
      (by simpa only [q, AddGroupSeminorm.comp_apply, Prod.forall] using hspan)

end List
