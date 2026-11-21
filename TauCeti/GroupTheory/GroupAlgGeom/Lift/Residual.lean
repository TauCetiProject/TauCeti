/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic

/-!
# Residual systems and reconstruction words

Let `S₂ ⊆ G[P]` be a system in lower variables `P` and `S ⊆ G[Q ⊔ P]` a system in top variables
`Q` and the lower variables, every solution of which restricts to a solution of `S₂`; for the
equations of a triangular quasi-quadratic system, `S₂` is the system of its lower levels. Let
`T(Q, P, Z) = 1 ∧ W(Q, P, Z) ≠ 1` be a system with an inequation in further variables `Z`.

A *residual system* of `T ∧ W ≠ 1` over `S` relative to `S₂` is a system `Δ(P, M) = 1` with an
inequation `ω(P, M) ≠ 1` in the lower variables and new variables `M`, together with
*reconstruction words* `q(Q, P, M)` for the variables `Z`, such that

* the reconstruction words solve `T` at every point `θ` of a family of solutions of `S` that
  separates the coordinate group of `S`, for every solution `m` of `Δ(θ|_P, M) = 1`;
* the residual inequation forces the reconstructed inequation: if `(v, m)` solves `Δ` with
  `ω(v, m) ≠ 1` and `v` solves `S₂`, then some solution `(x, v)` of `S` over `v` has
  `W(x, v, q(x, v, m)) ≠ 1`.

Then a lift of the residual system to the generic point of `S₂` gives a lift of `T ∧ W ≠ 1` to
the generic point of `S`: the residual values found in the coordinate group of `S₂` are carried
into the coordinate group of `S`, and the reconstruction words evaluated there solve `T` and keep
`W` nontrivial. This is the step "variables `M` can be found as elements of `G₂`, and variables
`Y` as elements of `G₁`" of the induction on levels in the implicit function theorem for regular
NTQ systems ([IFT], §7.6, proof of Theorem 11). Only the separation of coordinate groups by their
points is used: no discrimination property of the coordinate group of `S₂` is needed.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.IsResidual`: `(Δ, ω, q)` is a residual system of `T ∧ W ≠ 1` over
  `S` relative to `S₂`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.IsResidual.hasLiftNe`: a lift of a residual system to the generic
  point of `S₂` gives a lift of `T ∧ W ≠ 1` to the generic point of `S`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.6, Theorem 11 and its proof; §7.4, the end of the proof of Theorem 9.
* [LIFT] O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions
  into generic points*, Contemp. Math. 378 (2005), §8, proof of Theorem B.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod

variable {G H P Q M Z : Type*} [Group G] [Group H]

/-- `(Δ, ω, q)` is a *residual system* of `T(Q, P, Z) = 1 ∧ W(Q, P, Z) ≠ 1` over `S ⊆ G[Q ⊔ P]`
relative to the lower system `S₂ ⊆ G[P]`: the reconstruction words `q(Q, P, M)` for the variables
`Z` solve `T` at every point of a family of solutions of `S` separating its coordinate group,
whenever the new variables `M` solve the residual system `Δ(P, M) = 1` over the lower part of the
point; and whenever `v` solves `S₂` and `m` solves `Δ(v, M) = 1` with `ω(v, m) ≠ 1`, the
reconstructed inequation `W ≠ 1` holds at some solution `(x, v)` of `S` over `v`. -/
structure IsResidual (ι : G →* H) (S₂ : Set (GX G P)) (S : Set (GX G (Q ⊕ P)))
    (T : Set (GX G ((Q ⊕ P) ⊕ Z))) (W : GX G ((Q ⊕ P) ⊕ Z)) (Δ : Set (GX G (P ⊕ M)))
    (ω : GX G (P ⊕ M)) (q : Z → GX G ((Q ⊕ P) ⊕ M)) : Prop where
  /-- The reconstruction words solve `T` on a family of solutions of `S` separating its coordinate
  group, for every solution of the residual system over the lower part of the point. -/
  exists_family : ∃ Θ ⊆ V ι S, I ι Θ ≤ Rad ι S ∧ ∀ θ ∈ Θ, ∀ m : M → H,
    Sum.elim (θ ∘ Sum.inr) m ∈ V ι Δ → Sum.elim θ (wordMap ι q (Sum.elim θ m)) ∈ V ι T
  /-- The residual inequation forces the reconstructed inequation at a solution of `S` over the
  same lower point. -/
  exists_ne : ∀ v ∈ V ι S₂, ∀ m : M → H, Sum.elim v m ∈ V ι Δ → eval ι (Sum.elim v m) ω ≠ 1 →
    ∃ x : Q → H, Sum.elim x v ∈ V ι S ∧
      eval ι (Sum.elim (Sum.elim x v) (wordMap ι q (Sum.elim (Sum.elim x v) m))) W ≠ 1

/-- **Reconstruction from a residual system** ([IFT], §7.6, proof of Theorem 11). If every
solution of `S` restricts to a solution of the lower system `S₂`, and `(Δ, ω, q)` is a residual
system of `T ∧ W ≠ 1` over `S` relative to `S₂`, then a lift of `Δ ∧ ω ≠ 1` to the generic point
of `S₂` gives a lift of `T ∧ W ≠ 1` to the generic point of `S`. -/
theorem IsResidual.hasLiftNe {ι : G →* H} {S₂ : Set (GX G P)} {S : Set (GX G (Q ⊕ P))}
    {T : Set (GX G ((Q ⊕ P) ⊕ Z))} {W : GX G ((Q ⊕ P) ⊕ Z)} {Δ : Set (GX G (P ⊕ M))}
    {ω : GX G (P ⊕ M)} {q : Z → GX G ((Q ⊕ P) ⊕ M)} (hS : ∀ v ∈ V ι S, v ∘ Sum.inr ∈ V ι S₂)
    (h : IsResidual ι S₂ S T W Δ ω q) (hΔ : HasLiftNe ι S₂ Δ ω) : HasLiftNe ι S T W := by
  obtain ⟨Θ, hΘV, hΘ, hT⟩ := h.exists_family
  obtain ⟨m, hmΔ, hmω⟩ := hasLiftNe_iff.1 hΔ
  -- Words `m'` in `P` representing the residual values at the generic point of `S₂`.
  choose m' hm' using fun j => QuotientGroup.mk_surjective (m j)
  obtain rfl : wordMap (CoordGroup.coeff ι S₂) m' (CoordGroup.genericPoint ι S₂) = m :=
    funext fun j => by simp [hm']
  simp only [mem_V, ne_eq, eval_sumElim_wordMap, CoordGroup.eval_genericPoint,
    QuotientGroup.eq_one_iff] at hmΔ hmω
  have hΔv {v : P → H} (hv : v ∈ V ι S₂) : Sum.elim v (wordMap ι m' v) ∈ V ι Δ :=
    mem_V.2 fun d hd => (eval_sumElim_wordMap m' v d).trans (mem_Rad.1 (hmΔ d hd) v hv)
  -- The reconstruction words `y` in `Q ⊔ P`, with the words `m'` substituted for `M`.
  set y : Z → GX G (Q ⊕ P) := fun z => eval (inl : G →* GX G (Q ⊕ P))
    (Sum.elim (fun u => inr (FreeGroup.of u))
      fun j => Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr) (m' j)) (q z)
  have hy (v : Q ⊕ P → H) :
      wordMap ι y v = wordMap ι q (Sum.elim v (wordMap ι m' (v ∘ Sum.inr))) :=
    (wordMap_wordMap _ q v).symm.trans <| congrArg (wordMap ι q) <| funext fun j => by
      cases j <;> simp
  refine hasLiftNe_iff.2 ⟨wordMap (CoordGroup.coeff ι S) y (CoordGroup.genericPoint ι S),
    mem_V.2 fun t ht => ?_, fun hW => ?_⟩
  · rw [eval_sumElim_wordMap, CoordGroup.eval_genericPoint, QuotientGroup.eq_one_iff]
    exact hΘ <| mem_I.2 fun θ hθ => by
      simpa only [← eval_sumElim_wordMap, hy] using mem_V.1 (hT θ hθ _ (hΔv (hS θ (hΘV hθ)))) t ht
  · rw [eval_sumElim_wordMap, CoordGroup.eval_genericPoint, QuotientGroup.eq_one_iff] at hW
    obtain ⟨v, hv, hvω⟩ := not_forall₂.1 (mt mem_Rad.2 hmω)
    obtain ⟨x, hx, hxW⟩ := h.exists_ne v hv _ (hΔv hv) ((eval_sumElim_wordMap m' v ω).trans_ne hvω)
    exact hxW <| by
      simpa only [← eval_sumElim_wordMap, hy, Sum.elim_comp_inr] using mem_Rad.1 hW _ hx

section Examples

open FreeGroup
open scoped commutatorElement

/-- Over an empty level in variables `Q` above an empty level in variables `P`, the system
`[z, u] = 1 ∧ z ≠ 1`, for a lower variable `u`, has the residual system `[m, u] = 1 ∧ m ≠ 1` in a
new variable `m`, with the reconstruction `z = m`. The residual system is compatible with the
lower (empty) system over a nontrivial group, also at the points with `u = 1`, where the word
`z = u` vanishes; its lift `m = u` to the generic point of the lower system gives the lift
`z = u`. -/
example [Nontrivial H] (ι : G →* H) (u : P) (z : Z) (m : M) :
    IsResidual ι (∅ : Set (GX G P)) (∅ : Set (GX G (Q ⊕ P)))
        {⁅(inr (of (Sum.inr z)) : GX G ((Q ⊕ P) ⊕ Z)), inr (of (Sum.inl (Sum.inr u)))⁆}
        (inr (of (Sum.inr z))) {⁅(inr (of (Sum.inr m)) : GX G (P ⊕ M)), inr (of (Sum.inl u))⁆}
        (inr (of (Sum.inr m))) (fun _ => inr (of (Sum.inr m))) ∧
      IsCompatibleNe ι (∅ : Set (GX G P))
        {⁅(inr (of (Sum.inr m)) : GX G (P ⊕ M)), inr (of (Sum.inl u))⁆} (inr (of (Sum.inr m))) ∧
      HasLiftNe ι (∅ : Set (GX G (Q ⊕ P)))
        {⁅(inr (of (Sum.inr z)) : GX G ((Q ⊕ P) ⊕ Z)), inr (of (Sum.inl (Sum.inr u)))⁆}
        (inr (of (Sum.inr z))) := by
  obtain ⟨c, hc⟩ := exists_ne (1 : H)
  refine ⟨?h, isCompatibleNe_commutator_iff.2 ‹_›, IsResidual.hasLiftNe (by simp) ?h
    (hasLiftNe_commutator_iff.2 (nontrivial_of_ne (CoordGroup.genericPoint ι ∅ u) 1
      (CoordGroup.genericPoint_ne_one_iff.2 ⟨fun _ => c, by simp, hc⟩)))⟩
  exact ⟨⟨Set.univ, by simp, by simp, fun θ _ n hn => mem_V_commutator_iff.2 <| by
      simpa using mem_V_commutator_iff.1 hn⟩, fun v _ n _ hn => ⟨1, by simp, by simpa using hn⟩⟩

end Examples

end TauCeti.GroupAlgGeom.Lift
