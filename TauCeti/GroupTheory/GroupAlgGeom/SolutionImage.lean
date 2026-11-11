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

* If `K` is separated by `H` over `G`, an equation of `G[X]` vanishes on the image of `p` exactly
  when it vanishes at `p` in `K`. Hence, if an algebraic set `V(S)` is the union of the images of
  tuples `p j : X → K j` in groups separated by `H`, the radical of `S` is the intersection of the
  kernels of the evaluations at the `p j`.
* If `K` is discriminated by `H` over `G`, the image of `p` is irreducible in the Zariski
  topology.
* For a homomorphism `π : G[Y] → K` over `G`, not necessarily surjective, the kernel of `π` is its
  own radical when `K` is separated by `H`, and its algebraic set is irreducible when `K` is
  discriminated by `H`.

These statements are the interface between a cover of a solution set by the images of tuples in
groups discriminated by `H` (over a free group, groups given by triangular quasi-quadratic
systems) and the radical and the irreducible components of that solution set.

## Main results

* `TauCeti.GroupAlgGeom.IsSeparatedBy.I_range_comp_eq_ker_eval`: for `K` separated by `H`, the
  equations vanishing on the image of `p` are the kernel of the evaluation at `p`.
* `TauCeti.GroupAlgGeom.Rad_eq_iInf_ker_eval`: the radical of a system whose algebraic set is a
  union of images of tuples in groups separated by `H`.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.isIrreducible_range_comp`: the image of a tuple in a
  group discriminated by `H` is irreducible.
* `TauCeti.GroupAlgGeom.IsSeparatedBy.Rad_ker_eq`: for `K` separated by `H`, the kernel of a
  homomorphism `G[Y] → K` over `G` is its own radical.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.isIrreducible_V_ker`: for `K` discriminated by `H`, the
  algebraic set of that kernel is irreducible.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Lemmas 3 and 4.
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

/-- If `K` is separated by `H` over `G`, an equation vanishes on the image of a tuple `p` of
elements of `K` under all homomorphisms `K → H` over `G` exactly when it vanishes at `p`. -/
theorem IsSeparatedBy.I_range_comp_eq_ker_eval (h : IsSeparatedBy κ ι) (p : X → K) :
    I ι (Set.range fun ψ : GHom κ ι => ψ ∘ p) = (eval κ p).ker := by
  ext w
  simp only [mem_I, Set.forall_mem_range, ← map_eval, MonoidHom.mem_ker]
  refine ⟨fun hw => by_contra fun hne => ?_, fun hw ψ => by rw [hw, map_one]⟩
  obtain ⟨ψ, hψ⟩ := (isSeparatedBy_def _ _).1 h _ hne
  exact hψ (hw ψ)

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

/-- If `K` is separated by `H` over `G`, the kernel of a homomorphism `G[Y] → K` over `G` is its
own radical over `H`. -/
theorem IsSeparatedBy.Rad_ker_eq (h : IsSeparatedBy κ ι) (π : GHom (inl : G →* GX G Y) κ) :
    Rad ι ((π : GX G Y →* K).ker : Set (GX G Y)) = (π : GX G Y →* K).ker := by
  refine le_antisymm ?_ (subset_Rad _)
  rw [Rad_def]
  -- The points `ψ ∘ π ∘ vars` lie in `V(ker π)`, and exactly the equations of `ker π` vanish there.
  refine (I_antitone ι (range_comp_subset_V_ker π)).trans_eq ?_
  rw [h.I_range_comp_eq_ker_eval, eval_eq_of_comp_inl π.comp_coeff]

/-- If `K` is discriminated by `H` over `G`, the algebraic set over `H` of the kernel of a
homomorphism `G[Y] → K` over `G` is irreducible. -/
theorem IsDiscriminatedBy.isIrreducible_V_ker (h : IsDiscriminatedBy κ ι)
    (π : GHom (inl : G →* GX G Y) κ) :
    @IsIrreducible (Y → H) (zariskiTopology ι Y)
      (V ι ((π : GX G Y →* K).ker : Set (GX G Y))) := by
  have hRad := h.isSeparatedBy.Rad_ker_eq π
  rw [isIrreducible_V_iff_isDiscriminatedBy, CoordGroup.coeff_def]
  -- The coordinate group of the kernel embeds in `K` over `G`.
  exact h.of_injective ⟨QuotientGroup.lift _ (π : GX G Y →* K) hRad.le, fun g => by simp⟩
    ((QuotientGroup.injective_lift_iff _ _ hRad.le).2 hRad)

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
