/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Solutions parametrized by the homomorphisms of a group over the coefficients

Let `K` and `H` be groups over `G` and `p : X → K` a tuple of elements of `K`. Composing with the
homomorphisms `K → H` over `G` gives a set of points `{ψ ∘ p}` of `H^X`, the *image* of `p`. This
file relates the image to the algebraic geometry of `H`.

* If an algebraic set `V(S)` is the union of the images of tuples `p j : X → K j` in groups
  separated by `H`, the radical of `S` is the intersection of the kernels of the evaluations at the
  `p j`, because an equation vanishes on the image of `p j` exactly when it vanishes at `p j`.
* If `K` is discriminated by `H` over `G`, the image of `p` is irreducible in the Zariski
  topology.

These statements are the interface between a cover of a solution set by the images of tuples in
groups discriminated by `H` (over a free group, groups given by triangular quasi-quadratic
systems) and the radical and the irreducible components of that solution set.

## Main results

* `TauCeti.GroupAlgGeom.Rad_eq_iInf_ker_eval`: the radical of a system whose algebraic set is a
  union of images of tuples in groups separated by `H`.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.isIrreducible_range_comp`: the image of a tuple in a
  group discriminated by `H` is irreducible.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II: Systems in
  triangular quasi-quadratic form and description of residually free groups*, J. Algebra 200
  (1998), §0, Theorem 2, and §11.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999).
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom

variable {G H K X Y : Type*} [Group G] [Group H] [Group K] {ι : G →* H} {κ : G →* K}

private theorem range_comp_subset_V_ker (π : GHom (inl : G →* GX G Y) κ) :
    (Set.range fun ψ : GHom κ ι => ψ ∘ fun y => (π : GX G Y →* K) (inr (FreeGroup.of y))) ⊆
      V ι ((π : GX G Y →* K).ker : Set (GX G Y)) := by
  rintro _ ⟨ψ, rfl⟩
  refine mem_V.2 fun s hs => ?_
  rw [← map_eval, eval_eq_of_comp_inl π.comp_coeff]
  exact (congrArg ψ hs).trans (map_one ψ)

private theorem V_ker_subset_range_comp (π : GHom (inl : G →* GX G Y) κ)
    (hπ : Function.Surjective π) : V ι ((π : GX G Y →* K).ker : Set (GX G Y)) ⊆
      Set.range fun ψ : GHom κ ι => ψ ∘ fun y => (π : GX G Y →* K) (inr (FreeGroup.of y)) := by
  intro v hv
  obtain ⟨χ, hχ, hχm⟩ := GX.exists_bijective_gHom_of_eq_ker π hπ rfl
  refine ⟨(GX.quotientEvalGHom v hv).comp (χ.symmOfBijective hχ), funext fun y => ?_⟩
  simp [← hχm]

/-- If `K` is discriminated by `H` over `G`, the image in `H^X` of a tuple of elements of `K`
under all homomorphisms `K → H` over `G` is irreducible in the Zariski topology. -/
theorem IsDiscriminatedBy.isIrreducible_range_comp (h : IsDiscriminatedBy κ ι) (p : X → K) :
    @IsIrreducible (X → H) (zariskiTopology ι X) (Set.range fun ψ : GHom κ ι => ψ ∘ p) := by
  let := zariskiTopology ι X
  let := zariskiTopology ι K
  -- With the elements of `K` as variables, the homomorphisms `K → H` over `G` form an
  -- irreducible algebraic set, and composing with `p` is a continuous word map.
  let π : GHom (inl : G →* GX G K) κ := evalGHom κ id
  have hπ : Function.Surjective π := fun k => ⟨inr (FreeGroup.of k), by simp [π]⟩
  have hV : V ι ((π : GX G K →* K).ker : Set (GX G K)) =
      Set.range fun ψ : GHom κ ι => (ψ : K → H) :=
    ((V_ker_subset_range_comp π hπ).antisymm (range_comp_subset_V_ker π)).trans
      (by simp [π, Function.comp_def])
  have hirr := (h.isIrreducible_V_ker π).image (wordMap ι fun x => inr (FreeGroup.of (p x)))
    (continuous_wordMap _).continuousOn
  rw [hV, ← Set.range_comp] at hirr
  convert hirr using 2
  ext ψ x
  simp

/-- If the algebraic set of `S` over `H` is the union of the images of tuples `p j` of elements of
groups `K j` separated by `H`, then the radical of `S` is the intersection of the kernels of the
evaluations at the `p j`. -/
theorem Rad_eq_iInf_ker_eval {J : Type*} {K : J → Type*} [∀ j, Group (K j)] {κ : ∀ j, G →* K j}
    (h : ∀ j, IsSeparatedBy (κ j) ι) (p : ∀ j, X → K j) {S : Set (GX G X)}
    (hS : V ι S = ⋃ j, Set.range fun ψ : GHom (κ j) ι => ψ ∘ p j) :
    Rad ι S = ⨅ j, (eval (κ j) (p j)).ker := by
  rw [Rad_def, hS, I_iUnion]
  exact iInf_congr fun j => (h j).I_range_comp_eq_ker_eval (p j)

end TauCeti.GroupAlgGeom
