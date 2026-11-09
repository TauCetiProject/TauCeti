/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Coherent
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel
import TauCeti.Data.Set.UnionLift
import TauCeti.Topology.Coherent

/-!
# Homotopy equivalences of unions of cofibration towers

Let `X` be the union of an increasing sequence of subspaces `K 0 ⊆ K 1 ⊆ ⋯`, each having the
homotopy extension property in the next, and suppose `X` carries the final topology of the
sequence: a subset of `X` is open as soon as its trace on every `K n` is. Such a sequence is a
`TauCeti.IsCofibrationExhaustion` of `X`. Typical examples are the skeleta of a CW complex, the
stages of a tower of CW subcomplexes, and the sublevels of a proper Morse function at an increasing
sequence of regular values.

The main theorem compares two such unions. Let `K` and `L` be cofibration exhaustions of `X` and
`Y`, and let `φ : X → Y` restrict, for every `n`, to a homotopy equivalence `K n ≃ₕ L n`. Then
`φ` is itself a homotopy equivalence (`TauCeti.IsCofibrationExhaustion.exists_homotopyEquiv`),
with a homotopy inverse carrying each `L n` into `K n`. No inverse data on the stages are needed.

The proof constructs the inverse stage by stage. Using the homotopy extension property of
`K n ⊆ K (n + 1)` and of `L n ⊆ L (n + 1)`, a homotopy inverse `g n` of the stage `n` equivalence,
with its homotopy `g n ∘ φ ≃ id`, extends to a homotopy inverse `g (n + 1)` of the next stage with a
homotopy extending the given one
(`TauCeti.HasHomotopyExtensionProperty.exists_inverse_extending_homotopy`). The resulting strictly
compatible maps and homotopies glue, by the final topologies of `Y` and of `I × X`, to a map
`g : Y → X` with `g ∘ φ ≃ id` (`TauCeti.IsCofibrationExhaustion.exists_comp_homotopic_id`). This
makes `g` a left inverse of `φ` up to homotopy only. But each `g n` is a homotopy equivalence, so
the same construction applied to `g` gives `k : X → Y` with `k ∘ g ≃ id`. Then `g` has the left
inverse `k` and the right inverse `φ` up to homotopy, so `k ≃ φ`, and `φ ∘ g ≃ k ∘ g ≃ id`.

## Main definitions

* `TauCeti.IsCofibrationExhaustion`: an increasing covering sequence of subspaces, each having the
  homotopy extension property in the next, whose union carries the final topology.

## Main results

* `TauCeti.IsCofibrationExhaustion.exists_comp_homotopic_id`: stagewise homotopy equivalences glue
  to a left homotopy inverse of the union map, which is again a stagewise homotopy equivalence.
* `TauCeti.IsCofibrationExhaustion.exists_homotopyEquiv`: **a map of cofibration exhaustions
  which is a homotopy equivalence on every stage is a homotopy equivalence.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19 and its proof, for the stagewise extension of homotopy inverses.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.5, where the sublevels of a Morse function are compared with a CW complex
  built stage by stage.
-/

public section

noncomputable section

namespace TauCeti

open Set ContinuousMap unitInterval Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- An **exhaustion of `X` by cofibrations** is an increasing sequence `K 0 ⊆ K 1 ⊆ ⋯` of
subspaces covering `X`, each having the homotopy extension property in the next, such that `X`
carries the final topology of the sequence: a subset of `X` is open as soon as its trace on every
`K n` is open in `K n`. -/
structure IsCofibrationExhaustion (K : ℕ → Set X) : Prop where
  /-- The stages increase. -/
  monotone : Monotone K
  /-- The stages cover the space. -/
  iUnion_eq : ⋃ n, K n = univ
  /-- The space carries the final topology of its stages. -/
  isCoherentWith : IsCoherentWith (range K)
  /-- Each stage has the homotopy extension property in the next. -/
  hasHomotopyExtensionProperty (n : ℕ) :
    HasHomotopyExtensionProperty (((↑) : K (n + 1) → X) ⁻¹' K n)

namespace IsCofibrationExhaustion

variable {K : ℕ → Set X} {L : ℕ → Set Y}

/-- Every point lies in some stage. -/
theorem exists_mem (hK : IsCofibrationExhaustion K) (x : X) : ∃ n, x ∈ K n :=
  mem_iUnion.1 (hK.iUnion_eq.symm ▸ mem_univ x)

/-- **One step of the construction of a left inverse.** A homotopy inverse of the stage `n`
equivalence, with its homotopy, extends to a homotopy inverse of the stage `n + 1` equivalence
with an extending homotopy. -/
private theorem exists_succ (hK : IsCofibrationExhaustion K) (hL : IsCofibrationExhaustion L)
    {φ : C(X, Y)} (e : ∀ n, K n ≃ₕ L n) (he : ∀ n (x : K n), (e n x : Y) = φ x) (n : ℕ)
    (g : C(L n, K n)) (H : (g.comp (e n).toFun).Homotopy (ContinuousMap.id (K n))) :
    ∃ (g' : C(L (n + 1), K (n + 1)))
      (H' : (g'.comp (e (n + 1)).toFun).Homotopy (ContinuousMap.id (K (n + 1)))),
      (∀ (y : Y) (hy : y ∈ L n), (g' ⟨y, hL.monotone n.le_succ hy⟩ : X) = g ⟨y, hy⟩) ∧
      ∀ (t : I) (x : X) (hx : x ∈ K n),
        (H' (t, ⟨x, hK.monotone n.le_succ hx⟩) : X) = H (t, ⟨x, hx⟩) := by
  let A : Set (K (n + 1)) := (↑) ⁻¹' K n
  let B : Set (L (n + 1)) := (↑) ⁻¹' L n
  have hKn : K n ⊆ range ((↑) : K (n + 1) → X) := Subtype.range_coe.symm ▸ hK.monotone n.le_succ
  have hLn : L n ⊆ range ((↑) : L (n + 1) → Y) := Subtype.range_coe.symm ▸ hL.monotone n.le_succ
  let ιK : K n ≃ₜ A := (IsEmbedding.subtypeVal.homeomorphOfSubsetRange hKn).symm
  let ιL : L n ≃ₜ B := (IsEmbedding.subtypeVal.homeomorphOfSubsetRange hLn).symm
  have hιK' (a : A) : ((ιK.symm a : K n) : X) = a :=
    IsEmbedding.subtypeVal.homeomorphOfSubsetRange_apply_coe hKn a
  have hιL' (b : B) : ((ιL.symm b : L n) : Y) = b :=
    IsEmbedding.subtypeVal.homeomorphOfSubsetRange_apply_coe hLn b
  have hιK (a : K n) : ((ιK a : K (n + 1)) : X) = a := by
    rw [← hιK', Homeomorph.symm_apply_apply]
  have hιL (b : L n) : ((ιL b : L (n + 1)) : Y) = b := by
    rw [← hιL', Homeomorph.symm_apply_apply]
  let h₀ := ιK.symm.toHomotopyEquiv.trans ((e n).trans ιL.toHomotopyEquiv)
  have hh₀ : ∀ a, (h₀ a : L (n + 1)) = e (n + 1) a := fun a ↦ Subtype.ext <| by
    simp only [h₀, HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv]
    rw [hιL, he, he, hιK']
  let g₀ : C(B, A) := (ιK : C(K n, A)).comp (g.comp (ιL.symm : C(B, L n)))
  let H₀ : (g₀.comp h₀.toFun).Homotopy (ContinuousMap.id A) :=
    ((Homotopy.refl (ιK : C(K n, A))).comp (H.compContinuousMap (ιK.symm : C(A, K n)))).cast
      (ContinuousMap.ext fun _ ↦ by
        simp only [g₀, h₀, HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv, comp_apply,
          ContinuousMap.coe_ofClass, Homeomorph.symm_apply_apply])
      (ContinuousMap.ext fun _ ↦ by simp)
  obtain ⟨g', H', hg', hH', -⟩ :=
    (hK.hasHomotopyExtensionProperty n).exists_inverse_extending_homotopy
      (hL.hasHomotopyExtensionProperty n) (e (n + 1)) h₀ hh₀ g₀ H₀
  refine ⟨g', H', fun y hy ↦ ?_, fun t x hx ↦ ?_⟩
  · have hy' : ιL.symm ⟨⟨y, hL.monotone n.le_succ hy⟩, hy⟩ = ⟨y, hy⟩ :=
      Subtype.ext (hιL' _)
    refine (congrArg (fun z : K (n + 1) ↦ (z : X)) (hg' ⟨⟨y, _⟩, hy⟩)).trans ?_
    simp only [g₀, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, hy']
    exact hιK _
  · have hx' : ιK.symm ⟨⟨x, hK.monotone n.le_succ hx⟩, hx⟩ = ⟨x, hx⟩ :=
      Subtype.ext (hιK' _)
    refine (congrArg (fun z : K (n + 1) ↦ (z : X)) (hH' t ⟨⟨x, _⟩, hx⟩)).trans ?_
    simp only [H₀, Homotopy.cast_apply, Homotopy.comp_apply, Homotopy.refl_apply,
      Homotopy.compContinuousMap_apply, ContinuousMap.coe_ofClass, hx']
    exact hιK _

/-- **Compatible left inverses on all stages.** Homotopy inverses of the stage equivalences,
with homotopies `g n ∘ e n ≃ id`, can be chosen to extend one another. -/
private theorem exists_stages (hK : IsCofibrationExhaustion K) (hL : IsCofibrationExhaustion L)
    {φ : C(X, Y)} (e : ∀ n, K n ≃ₕ L n) (he : ∀ n (x : K n), (e n x : Y) = φ x) :
    ∃ (g : ∀ n, C(L n, K n))
      (H : ∀ n, ((g n).comp (e n).toFun).Homotopy (ContinuousMap.id (K n))),
      (∀ n (y : Y) (hy : y ∈ L n), (g (n + 1) ⟨y, hL.monotone n.le_succ hy⟩ : X) = g n ⟨y, hy⟩) ∧
      ∀ n (t : I) (x : X) (hx : x ∈ K n),
        (H (n + 1) (t, ⟨x, hK.monotone n.le_succ hx⟩) : X) = H n (t, ⟨x, hx⟩) := by
  choose g' H' hg' hH' using hK.exists_succ hL e he
  let S : ∀ n, Σ g : C(L n, K n), (g.comp (e n).toFun).Homotopy (ContinuousMap.id (K n)) :=
    fun n ↦ Nat.rec ⟨(e 0).invFun, (e 0).left_inv.some⟩ (fun n s ↦ ⟨g' n s.1 s.2, H' n s.1 s.2⟩) n
  exact ⟨fun n ↦ (S n).1, fun n ↦ (S n).2, fun n ↦ hg' n _ _, fun n ↦ hH' n _ _⟩

/-- **Stagewise homotopy equivalences glue to a left homotopy inverse.** Let `K` and `L` be
cofibration exhaustions of `X` and `Y`, and let `φ : X → Y` restrict on each stage to a homotopy
equivalence `e n : K n ≃ₕ L n`. Then there is `g : Y → X` with `g ∘ φ` homotopic to the identity,
which restricts on each stage to a homotopy equivalence `e' n : L n ≃ₕ K n`. -/
theorem exists_comp_homotopic_id (hK : IsCofibrationExhaustion K) (hL : IsCofibrationExhaustion L)
    (φ : C(X, Y)) (e : ∀ n, K n ≃ₕ L n) (he : ∀ n (x : K n), (e n x : Y) = φ x) :
    ∃ (g : C(Y, X)) (e' : ∀ n, L n ≃ₕ K n), (∀ n (y : L n), (e' n y : X) = g y) ∧
      (g.comp φ).Homotopic (ContinuousMap.id X) := by
  obtain ⟨g, H, hg, hH⟩ := hK.exists_stages hL e he
  let G := liftCover L (fun n y ↦ (g n y : X))
    (hL.monotone.eq_of_forall_succ_eq (fun n y ↦ (g n y : X)) hg) hL.iUnion_eq
  have hG : ∀ n (y : L n), G y = g n y := fun _ ↦ liftCover_coe
  have hGc : Continuous G := hL.isCoherentWith.continuous_liftCover (fun n ↦ by fun_prop) _ _
  let P : ℕ → Set (I × X) := fun n ↦ univ ×ˢ K n
  have hP : ⋃ n, P n = univ := by rw [← prod_iUnion, hK.iUnion_eq, univ_prod_univ]
  let F := liftCover P (fun n p ↦ (H n (p.1.1, ⟨p.1.2, p.2.2⟩) : X))
    (fun m n p hm hn ↦ hK.monotone.eq_of_forall_succ_eq (fun n x ↦ (H n (p.1, x) : X))
      (fun n x hx ↦ hH n p.1 x hx) m n p.2 hm.2 hn.2) hP
  have hF : ∀ n t (x : K n), F (t, x) = H n (t, x) := fun n t x ↦
    liftCover_of_mem (S := P) (i := n) ⟨mem_univ t, x.2⟩
  have hFc : Continuous F := by
    refine IsCoherentWith.continuous_liftCover ?_ (fun n ↦ by fun_prop) _ hP
    rw [show P = (univ ×ˢ ·) ∘ K from rfl, range_comp]
    exact hK.isCoherentWith.univ_prod (by rw [sUnion_range, hK.iUnion_eq])
  have hF₀ : ∀ x, F (0, x) = G (φ x) := fun x ↦ by
    obtain ⟨n, hx⟩ := hK.exists_mem x
    rw [hF n 0 ⟨x, hx⟩, Homotopy.apply_zero, ← he n ⟨x, hx⟩, hG n, ContinuousMap.comp_apply]
  have hF₁ : ∀ x, F (1, x) = x := fun x ↦ by
    obtain ⟨n, hx⟩ := hK.exists_mem x
    rw [hF n 1 ⟨x, hx⟩, Homotopy.apply_one, ContinuousMap.id_apply]
  refine ⟨⟨G, hGc⟩, fun n ↦ ⟨g n, (e n).toFun, ?_, ⟨H n⟩⟩, fun n y ↦ (hG n y).symm,
    ⟨⟨⟨F, hFc⟩, hF₀, hF₁⟩⟩⟩
  exact (e n).toFun_comp_homotopic_id_of_comp_toFun_homotopic_id ⟨H n⟩

/-- **A map of cofibration exhaustions which is a homotopy equivalence on every stage is a
homotopy equivalence.** Let `K` and `L` be cofibration exhaustions of `X` and `Y`, and let
`φ : X → Y` restrict on each stage to a homotopy equivalence `K n ≃ₕ L n`. Then `φ` is a homotopy
equivalence, with a homotopy inverse carrying each `L n` into `K n`. -/
theorem exists_homotopyEquiv (hK : IsCofibrationExhaustion K) (hL : IsCofibrationExhaustion L)
    (φ : C(X, Y)) (e : ∀ n, K n ≃ₕ L n) (he : ∀ n (x : K n), (e n x : Y) = φ x) :
    ∃ E : X ≃ₕ Y, E.toFun = φ ∧ ∀ n, MapsTo E.symm (L n) (K n) := by
  obtain ⟨g, e', he', hgφ⟩ := hK.exists_comp_homotopic_id hL φ e he
  obtain ⟨k, -, -, hkg⟩ := hL.exists_comp_homotopic_id hK g e' he'
  have hkφ : k.Homotopic φ := hkg.homotopic_of_comp_homotopic_id hgφ
  refine ⟨⟨φ, g, hgφ, (hkφ.symm.comp (.refl g)).trans hkg⟩, rfl, fun n y hy ↦ ?_⟩
  exact he' n ⟨y, hy⟩ ▸ (e' n ⟨y, hy⟩).2

end IsCofibrationExhaustion

end TauCeti
