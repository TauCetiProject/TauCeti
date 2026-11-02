/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass
import TauCeti.Data.List.ProdOfFn

/-!
# Trace pairings detecting Hochschild classes of zigzag algebras in every arity

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). A minimal `A∞` deformation of `Z` whose first higher
operation is `m_{n+2}` has that operation as its obstruction, a Hochschild cocycle in
`HH^{n+2, -n}(Z, Z)`. This file gives a supply of linear functionals on suspended Hochschild
cochains which vanish on all coboundaries of degree zero, so that a cocycle on which one of them is
nonzero is not a coboundary.

## The word pairing

Fix weights `a w` on the words `w = (w 0, …, w (n + 1))` of `n + 2` darts of `G`. The **word
pairing** (`TauCeti.zigzagWordPairing`) is

```text
Λ_a(F) = ∑ w, a w · tr F(a_{w 0}, …, a_{w (n+1)}),
```

where `a_d` is the arrow of the dart `d` and `tr` is the Frobenius trace
`TauCeti.zigzagTrace`, nonzero exactly on the volume classes. It vanishes on every Hochschild
coboundary of degree zero (`TauCeti.zigzagWordPairing_hochschildDifferential_eq_zero`) as soon as
the weights satisfy two conditions.

* **Anticyclicity**: moving the first dart of a word to the end changes the sign of its weight,
  `a (u, e) = -a (e, u)`.
* **The signless relation in every position**: for every vertex `v`, the sum of the weights of the
  words carrying the backtrack `d, d.symm` based at `v` in two given consecutive positions, over
  all darts `d` with head `v`, vanishes.

On a word of arrows the Hochschild differential of a degree-zero suspended cochain `φ` is

```text
δφ(x₀, …, x_{n+1}) = ∑_p φ(x₀, …, x_p x_{p+1}, …, x_{n+1})
                       - φ(x₀, …, x_n) x_{n+1} - x₀ φ(x₁, …, x_{n+1})
```

(`TauCeti.zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod_of_mem`). The two
outer terms cancel in `Λ_a` by the trace property `tr(xy) = tr(yx)` and anticyclicity. In an inner
term the product of two arrows is the volume class `x_v` when they form a backtrack based at `v`,
and zero otherwise, so the inner terms cancel by the signless relation.

## Weights from preprojective functionals

The second condition says that `a` vanishes on the signless preprojective relation
`∑_{d.snd = v} d d.symm` in every position, which is the local relation of the quadratic dual of
`Z` found by Huerfano and Khovanov. Accordingly, let `β` send each dart to an element of a
semiring `B` with a `k`-module structure, such as a `k`-algebra, such that
`∑_{d.snd = v} β d * β d.symm = 0` at every vertex `v`: for example the classes of the arrows in the
signless preprojective algebra `TauCeti.signlessPreprojectiveAlgebra`, or their matrices in one of
its representations. Let `f` be a linear functional on `B` which is **anticyclic on the arrows**:
`f (y * β e) = -f (β e * y)`. Then the weights `a w = f (β (w 0) ⋯ β (w (n + 1)))` satisfy both
conditions, and `Λ_a` vanishes on coboundaries
(`TauCeti.zigzagWordPairing_hochschildDifferential_eq_zero_of_anticyclic`).

For instance, on a bipartite graph with a sign `ε v = ±1` changing along every edge, the element
`s = ∑ ε v e_v` of the signless preprojective algebra anticommutes with every arrow, so
`f y = g (s * y)` is anticyclic on the arrows for every linear functional `g` vanishing on
commutators. In this way cyclic classes of signless preprojective algebras in positive degree are
paired with Hochschild classes of `Z`.

The backtrack pairing `TauCeti.zigzagBacktrackPairing` is the word pairing of length four with
weights supported on backtrack walks.

## Main definitions

* `TauCeti.zigzagWordPairing`: the word pairing `Λ_a` on suspended Hochschild cochains.

## Main results

* `TauCeti.zigzagWordPairing_hochschildDifferential_eq_zero`: `Λ_a` vanishes on coboundaries of
  degree zero when its weights are anticyclic and satisfy the signless relation in every position.
* `TauCeti.zigzagWordPairing_hochschildDifferential_eq_zero_of_anticyclic`: the same for the
  weights given by an anticyclic functional on an algebra receiving the signless relations.
* `TauCeti.not_exists_hochschildDifferential_eq_of_zigzagWordPairing_ne_zero`: a cochain on which
  such a pairing is nonzero is not a Hochschild coboundary of degree zero.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4, for the
  quadratic dual of the zigzag algebra.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Sections 3 and 4, for the comparison of zigzag Hochschild cohomology with the cyclic quotient of
  the preprojective algebra.
* J.-L. Loday, *Cyclic Homology*, Chapter 1, for Hochschild chains and cochains and their duality.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

/-! ### The word pairing -/

section Pairing

variable [Fintype G.Dart]

variable (hns) in
/-- **The word pairing** with weights `a w` on the words of `n + 2` darts: the linear functional on
suspended Hochschild cochains `F` of the zigzag algebra

```text
Λ_a(F) = ∑ w, a w · tr F(a_{w 0}, …, a_{w (n+1)}),
```

where `a_d` is the arrow of the dart `d`. It is the pairing, through the trace, with the Hochschild
chain `∑ w, a w (1 ⊗ a_{w 0} ⊗ ⋯ ⊗ a_{w (n+1)})`. -/
noncomputable def zigzagWordPairing (n : ℕ) (a : (Fin (n + 2) → G.Dart) → k) :
    (ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G)
      →ₗ[k] k :=
  ∑ w, a w • (zigzagTrace k G hns ∘ₗ
    LinearMap.applyₗ (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t))))

/-- Unfolding the word pairing. -/
theorem zigzagWordPairing_apply (n : ℕ) (a : (Fin (n + 2) → G.Dart) → k)
    (F : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) :
    zigzagWordPairing hns n a F = ∑ w, a w *
      zigzagTrace k G hns (F (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t))))
    := by
  simp [zigzagWordPairing, LinearMap.sum_apply]

/-- The outer terms of the Hochschild differential cancel in the word pairing of anticyclic
weights. Here `α` stands for the arrows, abstracted so that words can be rewritten freely. -/
private theorem sum_trace_outer_eq_zero {n : ℕ} {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (α : G.Dart → nonisolatedZigzagQuotient k G)
    (φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) :
    ∑ w : Fin (n + 2) → G.Dart, a w * zigzagTrace k G hns
        (φ (subword k (fun t ↦ α (w t)) 0 (n + 1)) * α (w (Fin.last (n + 1)))) +
      ∑ w : Fin (n + 2) → G.Dart, a w * zigzagTrace k G hns
        (α (w 0) * φ (subword k (fun t ↦ α (w t)) 1 (n + 1))) = 0 := by
  rw [← (Fin.snocEquiv fun _ ↦ G.Dart).sum_comp, ← (Fin.consEquiv fun _ ↦ G.Dart).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  -- Both outer blocks are the word of `u`.
  have hinit : subword k (fun t ↦ α ((Fin.snoc u e : Fin (n + 2) → G.Dart) t)) 0 (n + 1) =
      subword k (fun t ↦ α (u t)) 0 (n + 1) :=
    subword_congr k _ _ (by omega) (by omega) fun j hj ↦ by
      rw [show (⟨0 + j, by omega⟩ : Fin (n + 2)) = Fin.castSucc ⟨0 + j, by omega⟩ from
        (Fin.castSucc_mk _ _ _).symm, Fin.snoc_castSucc]
  have htail : subword k (fun t ↦ α ((Fin.cons e u : Fin (n + 2) → G.Dart) t)) 1 (n + 1) =
      subword k (fun t ↦ α (u t)) 0 (n + 1) := by
    rw [show (fun t ↦ α ((Fin.cons e u : Fin (n + 2) → G.Dart) t)) =
        Fin.cons (α e) fun t ↦ α (u t) from Fin.comp_cons α e u, ← subword_tail, Fin.tail_cons]
  rw [Fin.snocEquiv_apply, Fin.consEquiv_apply, Fin.snoc_last, Fin.cons_zero, hinit, htail, hrot,
    zigzagTrace_mul_comm k G hns (α e), neg_mul, neg_add_cancel]

variable [DecidableEq V]

/-- The inner terms of the Hochschild differential at the position `p` cancel in the word pairing
of weights satisfying the signless relation there. Here `α` stands for the arrows, abstracted so
that words can be rewritten freely; only the products of two arrows enter. -/
private theorem sum_trace_inner_eq_zero {n : ℕ} {a : (Fin (n + 2) → G.Dart) → k} (p : Fin (n + 1))
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0)
    (α : G.Dart → nonisolatedZigzagQuotient k G)
    (hα : ∀ d e : G.Dart, e ≠ d.symm → α d * α e = 0)
    (hα' : ∀ d : G.Dart, α d * α d.symm = zigzagVolume k G d.snd)
    (φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) :
    ∑ w : Fin (n + 2) → G.Dart, a w * zigzagTrace k G hns (φ (splice k (fun t ↦ α (w t)) 0
      (n + 2) p 2 (α (w p.castSucc) * α (w p.succ)))) = 0 := by
  -- Write each word as `u` with the darts `d, e` inserted at the positions `p` and `p + 1`.
  rw [← (Fin.insertNthEquiv (fun _ ↦ G.Dart) p.castSucc).sum_comp, Fintype.sum_prod_type]
  simp_rw [← (Fin.insertNthEquiv (fun _ ↦ G.Dart) p).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, splice_two_eq_of_tprod_insertNth,
    Fin.insertNth_apply_same, ← Fin.succAbove_castSucc_self, Fin.insertNth_apply_succAbove]
  rw [Finset.sum_congr rfl fun d _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  -- Only the backtracks `d, d.symm` survive, collapsing to the volume class at the head of `d`.
  rw [Finset.sum_congr rfl fun d _ ↦ Finset.sum_eq_single d.symm (fun e _ he ↦ by
      rw [hα d e he, (PiTensorProduct.tprod k).map_coord_zero p (Fin.insertNth_apply_same _ _ _),
        map_zero, map_zero, map_zero, mul_zero]) (by simp)]
  simp only [hα']
  -- Group the darts by their head.
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun d : G.Dart ↦ d.snd)
    (t := Finset.univ.image fun d : G.Dart ↦ d.snd) fun d _ ↦
      Finset.mem_image_of_mem _ (Finset.mem_univ d)]
  refine Finset.sum_eq_zero fun v _ ↦ ?_
  rw [Finset.sum_congr rfl fun d hd ↦ by rw [(Finset.mem_filter.1 hd).2], ← Finset.sum_mul,
    hrel u v, zero_mul]

/-- **The word pairing vanishes on Hochschild coboundaries.** Let the weights `a` on words of
`n + 2` darts be anticyclic, `a (u, e) = -a (e, u)`, and satisfy the signless relation in every
pair of consecutive positions: for every vertex `v`, the weights of the words carrying a backtrack
`d, d.symm` based at `v` in the positions `p` and `p + 1`, summed over the darts `d` with head
`v`, add up to zero. Then the word pairing `Λ_a` vanishes on the Hochschild differential of every
suspended cochain of degree zero. -/
theorem zigzagWordPairing_hochschildDifferential_eq_zero {n : ℕ}
    {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (p : Fin (n + 1)) (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0)
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    zigzagWordPairing hns n a ((𝒵).hochschildDifferential 0 φ) = 0 := by
  rw [zigzagWordPairing_apply]
  simp only [zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_tprod_of_mem hφ _
      fun i ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _,
    map_sub, map_sum, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_eq_zero fun p _ ↦ sum_trace_inner_eq_zero p (hrel p)
    (fun d ↦ 𝔞 d) (fun d e he ↦ zigzagMk_ofArrow_mul_ofArrow_of_ne k G he)
    (zigzagMk_ofArrow_mul_ofArrow_symm k G) φ, sub_sub,
    sum_trace_outer_eq_zero hrot (fun d ↦ 𝔞 d) φ, sub_zero]

/-- **A cochain detected by a word pairing is not a coboundary.** If the weights `a` are anticyclic
and satisfy the signless relation in every pair of consecutive positions, and the word pairing
`Λ_a` does not vanish on `F`, then `F` is not the Hochschild differential of a suspended cochain of
degree zero. -/
theorem not_exists_hochschildDifferential_eq_of_zigzagWordPairing_ne_zero {n : ℕ}
    {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (p : Fin (n + 1)) (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0)
    {F : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hF : zigzagWordPairing hns n a F ≠ 0) :
    ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
        ((𝒵).grading.shift 1).piece 0 ∧ (𝒵).hochschildDifferential 0 φ = F := by
  rintro ⟨φ, hφ, rfl⟩
  exact hF (zigzagWordPairing_hochschildDifferential_eq_zero hrot hrel hφ)

end Pairing

/-! ### Weights from anticyclic functionals -/

section Anticyclic

variable {B : Type*} [Semiring B] [Module k B]

variable [Fintype G.Dart] [DecidableEq V]

/-- **Weights from an anticyclic functional.** Let `β` send each dart to an element of a semiring
`B` with a `k`-module structure, such that the signless relation
`∑_{d.snd = v} β d * β d.symm = 0` holds at every vertex `v`, and let `f` be a linear functional on
`B` which is anticyclic on these elements: `f (y * β e) = -f (β e * y)`. Then the word pairing with
weights `a w = f (β (w 0) ⋯ β (w (n + 1)))` vanishes on the Hochschild differential of every
suspended cochain of degree zero.

For the signless preprojective algebra of a bipartite graph and `β` the classes of the arrows, `f`
can be a functional vanishing on commutators, twisted by the element `∑ ε v e_v` for a sign `ε`
changing along every edge. -/
theorem zigzagWordPairing_hochschildDifferential_eq_zero_of_anticyclic {n : ℕ}
    (β : G.Dart → B) (hβ : ∀ v : V, ∑ d : G.Dart with d.snd = v, β d * β d.symm = 0)
    (f : B →ₗ[k] k) (hf : ∀ (e : G.Dart) (y : B), f (y * β e) = -f (β e * y))
    {φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    zigzagWordPairing hns n (fun w ↦ f (List.ofFn fun t ↦ β (w t)).prod)
      ((𝒵).hochschildDifferential 0 φ) = 0 := by
  refine zigzagWordPairing_hochschildDifferential_eq_zero (fun u e ↦ ?_) (fun p u v ↦ ?_) hφ
  · have hsnoc : (List.ofFn fun t ↦ β ((Fin.snoc u e : Fin (n + 2) → G.Dart) t)).prod =
        (List.ofFn fun t ↦ β (u t)).prod * β e := by
      rw [List.ofFn_succ' (n := n + 1), List.concat_eq_append, List.prod_append,
        List.prod_singleton]
      simp
    have hcons : (List.ofFn fun t ↦ β ((Fin.cons e u : Fin (n + 2) → G.Dart) t)).prod =
        β e * (List.ofFn fun t ↦ β (u t)).prod := by
      rw [show (fun t ↦ β ((Fin.cons e u : Fin (n + 2) → G.Dart) t)) =
          Fin.cons (β e) fun t ↦ β (u t) from Fin.comp_cons β e u, List.ofFn_cons, List.prod_cons]
    rw [hsnoc, hcons, hf]
  · obtain ⟨L, R, h⟩ := List.exists_prod_ofFn_insertNth_insertNth β p u
    simp_rw [h]
    calc ∑ d : G.Dart with d.snd = v, f (L * β d * β d.symm * R)
        = f (L * (∑ d : G.Dart with d.snd = v, β d * β d.symm) * R) := by
          rw [Finset.mul_sum, Finset.sum_mul, map_sum]
          simp only [mul_assoc]
      _ = 0 := by rw [hβ, mul_zero, zero_mul, map_zero]

end Anticyclic

end TauCeti
