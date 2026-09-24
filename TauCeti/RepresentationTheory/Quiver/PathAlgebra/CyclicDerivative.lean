/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Cyclic derivatives in a path algebra

Let `a : i ⟶ j` be an arrow of a finite quiver `Q`. The **cyclic derivative** `∂_a` is the
linear endomorphism of the path algebra `kQ` which, on a cycle, deletes one occurrence of `a` and
reads the rest of the cycle starting just after it, summed over all occurrences of `a`: if the
cycle traverses `v`, then `a`, then `u`, the occurrence contributes the path traversing `u` and
then `v`, a path from `j` back to `i`. In Tau Ceti's later-factor-first convention this
contribution is the product `ofPath v * ofPath u`. A path which is not a cycle has no such
rearrangement and has cyclic derivative `0`. Cyclic derivatives of a potential `W`, a linear
combination of cycles, are the relations of the Jacobian algebra of `(Q, W)` and the
differentials of the reverse arrows in its three-dimensional Ginzburg differential graded algebra.

The basic identity satisfied by cyclic derivatives is

```text
∑_a a ∂_a(x) = ∑_a ∂_a(x) a,
```

the sums running over all arrows of `Q`, for every `x ∈ kQ`. On a cycle both sides are the sum of
all its rotations, one for each of its arrows. The identity holds vertex by vertex as well: the
arrows `a` with head `v` on the left and those with tail `v` on the right give equal sums. This
is what makes the square of the three-dimensional Ginzburg differential vanish on the adjoined
loops.

## Main definitions

* `TauCeti.PathAlgebra.cyclicDerivative`: the cyclic derivative `∂_a` with respect to an arrow.

## Main results

* `TauCeti.PathAlgebra.vertexIdempotent_mul_cyclicDerivative` and
  `TauCeti.PathAlgebra.cyclicDerivative_mul_vertexIdempotent`: the cyclic derivative with respect
  to `a : i ⟶ j` lies in the corner of `kQ` of paths from `j` to `i`.
* `TauCeti.PathAlgebra.cyclicDerivative_ofPath`: the cyclic derivative of a cycle is the sum, over
  the occurrences of the arrow, of the rotated remainders.
* `TauCeti.PathAlgebra.cyclicDerivative_ofPath_of_ne`: a path which is not a cycle has cyclic
  derivative `0`.
* `TauCeti.PathAlgebra.cyclicDerivative_mul_comm`: **the cyclic derivative is invariant under
  cyclic permutation**, `∂_a(xy) = ∂_a(yx)`.
* `TauCeti.PathAlgebra.cyclicDerivative_ofArrow_self` and
  `TauCeti.PathAlgebra.cyclicDerivative_ofArrow_of_ne`: the cyclic derivatives of an arrow.
* `TauCeti.PathAlgebra.sum_ofArrow_mul_cyclicDerivative_eq_sum_cyclicDerivative_mul_ofArrow`:
  **the local cyclic identity** at a vertex `v`,
  `∑_{head a = v} a ∂_a(x) = ∑_{tail a = v} ∂_a(x) a`.
* `TauCeti.PathAlgebra.sum_sum_sum_ofArrow_mul_cyclicDerivative_comm`: **the global cyclic
  identity** `∑_a a ∂_a(x) = ∑_a ∂_a(x) a`.

## References

* H. Derksen, J. Weyman and A. Zelevinsky, *Quivers with potentials and their representations I:
  Mutations*, Section 3, where cyclic derivatives are defined and shown to vanish on commutators.
* V. Ginzburg, *Calabi--Yau algebras*, Section 4.2, where the cyclic identity is the vanishing of
  the square of the Ginzburg differential on the adjoined loops.
-/

public section

namespace TauCeti

namespace PathAlgebra

universe u v w

section Path

variable (k : Type w) [CommSemiring k] {Q : Type u} [Quiver.{v} Q]

open scoped Classical in
/-- The sum, over the ways of writing a path `p` as a path `v`, then the arrow `a : i ⟶ j`, then a
path `u`, of `ofPath v * y * ofPath u * e_j`. The cyclic derivative is the value at `y = 1`; the
general `y` is the accumulator of the recursion along the last arrow of `p`. -/
private noncomputable def cyclicDerivativePath {i j : Q} (a : i ⟶ j) :
    ∀ {s t : Q}, _root_.Quiver.Path s t → pathAlgebra k Q → pathAlgebra k Q
  | _, _, .nil, _ => 0
  | _, _, .cons p e, y =>
      (if (⟨_, _, e⟩ : Σ x z : Q, x ⟶ z) = ⟨i, j, a⟩ then
        ofPath ⟨_, _, p⟩ * y * vertexIdempotent k j else 0) +
        cyclicDerivativePath a p (y * ofArrow e)

variable {i j : Q} (a : i ⟶ j)

private theorem cyclicDerivativePath_nil (s : Q) (y : pathAlgebra k Q) :
    cyclicDerivativePath k a (.nil : _root_.Quiver.Path s s) y = 0 := by
  simp [cyclicDerivativePath]

open scoped Classical in
private theorem cyclicDerivativePath_cons {s m t : Q} (p : _root_.Quiver.Path s m) (e : m ⟶ t)
    (y : pathAlgebra k Q) :
    cyclicDerivativePath k a (p.cons e) y =
      (if (⟨m, t, e⟩ : Σ x z : Q, x ⟶ z) = ⟨i, j, a⟩ then
        ofPath ⟨s, m, p⟩ * y * vertexIdempotent k j else 0) +
        cyclicDerivativePath k a p (y * ofArrow e) := by
  rw [cyclicDerivativePath]

/-- The recursion lands in the left corner of the tail `i` of `a`. -/
private theorem vertexIdempotent_mul_cyclicDerivativePath {s t : Q} (p : _root_.Quiver.Path s t)
    (y : pathAlgebra k Q) :
    vertexIdempotent k i * cyclicDerivativePath k a p y = cyclicDerivativePath k a p y := by
  induction p generalizing y with
  | nil => rw [cyclicDerivativePath_nil, mul_zero]
  | cons p e ih =>
      rw [cyclicDerivativePath_cons, mul_add, ih]
      split_ifs with h
      · obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 h
        rw [← mul_assoc, ← mul_assoc, vertexIdempotent_mul_ofPath]
      · rw [mul_zero]

/-- The recursion lands in the right corner of the head `j` of `a`. -/
private theorem cyclicDerivativePath_mul_vertexIdempotent {s t : Q} (p : _root_.Quiver.Path s t)
    (y : pathAlgebra k Q) :
    cyclicDerivativePath k a p y * vertexIdempotent k j = cyclicDerivativePath k a p y := by
  induction p generalizing y with
  | nil => rw [cyclicDerivativePath_nil, zero_mul]
  | cons p e ih =>
      rw [cyclicDerivativePath_cons, add_mul, ih]
      split_ifs
      · rw [mul_assoc _ (vertexIdempotent k j), vertexIdempotent_mul_self]
      · rw [zero_mul]

/-- The accumulator may be restricted to the corner of the source of the path. -/
private theorem cyclicDerivativePath_vertexIdempotent_mul {s t : Q} (p : _root_.Quiver.Path s t)
    (y : pathAlgebra k Q) :
    cyclicDerivativePath k a p (vertexIdempotent k s * y) = cyclicDerivativePath k a p y := by
  induction p generalizing y with
  | nil => rw [cyclicDerivativePath_nil, cyclicDerivativePath_nil]
  | cons p e ih =>
      rw [cyclicDerivativePath_cons, cyclicDerivativePath_cons, mul_assoc (vertexIdempotent k _) y,
        ih, ← mul_assoc (ofPath _) (vertexIdempotent k _), ofPath_mul_vertexIdempotent]

/-- The accumulator may be restricted to the corner of the target of the path. -/
private theorem cyclicDerivativePath_mul_vertexIdempotent_right {s t : Q}
    (p : _root_.Quiver.Path s t) (y : pathAlgebra k Q) :
    cyclicDerivativePath k a p (y * vertexIdempotent k t) = cyclicDerivativePath k a p y := by
  cases p with
  | nil => rw [cyclicDerivativePath_nil, cyclicDerivativePath_nil]
  | cons p e =>
      rw [cyclicDerivativePath_cons, cyclicDerivativePath_cons, mul_assoc y,
        ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]
      split_ifs with h
      · have htj : t = j := congrArg (fun x => x.2.1) h
        subst htj
        simp only [mul_assoc, vertexIdempotent_mul_self]
      · rfl

private theorem cyclicDerivativePath_zero {s t : Q} (p : _root_.Quiver.Path s t) :
    cyclicDerivativePath k a p 0 = 0 := by
  induction p with
  | nil => rw [cyclicDerivativePath_nil]
  | cons p e ih => rw [cyclicDerivativePath_cons, zero_mul, ih, mul_zero, zero_mul, ite_self,
      add_zero]

/-- **Concatenation.** An occurrence of `a` in `p` followed by `q` lies either in `q`, where the
part `p` before it is carried along with the accumulator, or in `p`, where the part `q` after it
is. -/
private theorem cyclicDerivativePath_comp {s t r : Q} (p : _root_.Quiver.Path s t)
    (q : _root_.Quiver.Path t r) (y : pathAlgebra k Q) :
    cyclicDerivativePath k a (p.comp q) y =
      cyclicDerivativePath k a q (ofPath ⟨s, t, p⟩ * y) +
        cyclicDerivativePath k a p (y * ofPath ⟨t, r, q⟩) := by
  induction q generalizing y with
  | nil =>
      rw [_root_.Quiver.Path.comp_nil, cyclicDerivativePath_nil, zero_add,
        ← vertexIdempotent_eq_ofPath, cyclicDerivativePath_mul_vertexIdempotent_right]
  | cons q e ih =>
      rw [_root_.Quiver.Path.comp_cons, cyclicDerivativePath_cons, cyclicDerivativePath_cons, ih,
        ← ofPath_mul_ofPath_of_comp, ← ofArrow_mul_ofPath]
      simp only [mul_assoc, add_assoc]

/-- A path has only finitely many decompositions as a path `v`, then `a`, then a path `u`: such a
decomposition is determined by the length of `v`. -/
private theorem finite_setOf_comp_toPath_comp_eq {s t : Q} (p : _root_.Quiver.Path s t) :
    {d : _root_.Quiver.Path s i × _root_.Quiver.Path j t |
      d.1.comp (a.toPath.comp d.2) = p}.Finite := by
  refine Set.Finite.of_finite_image (f := fun d => d.1.length)
    ((Set.finite_Iic p.length).subset ?_) ?_
  · rintro _ ⟨d, rfl, rfl⟩
    simp [_root_.Quiver.Path.length_comp]
  · rintro ⟨v, u⟩ hd ⟨v', u'⟩ hd' hl
    obtain ⟨rfl, h⟩ := (_root_.Quiver.Path.comp_inj' hl).1
      ((show v.comp (a.toPath.comp u) = p from hd).trans hd'.symm)
    rw [_root_.Quiver.Path.comp_inj_right.1 h]

/-- The recursion sums `ofPath v * y * ofPath u` over the decompositions of `p` as a path `v`, then
`a`, then a path `u`. -/
private theorem cyclicDerivativePath_eq_finsum {s t : Q} (p : _root_.Quiver.Path s t)
    (y : pathAlgebra k Q) :
    cyclicDerivativePath k a p y =
      ∑ᶠ d ∈ {d : _root_.Quiver.Path s i × _root_.Quiver.Path j t |
        d.1.comp (a.toPath.comp d.2) = p}, ofPath ⟨s, i, d.1⟩ * y * ofPath ⟨j, t, d.2⟩ := by
  induction p generalizing y with
  | nil =>
      have hempty : {d : _root_.Quiver.Path s i × _root_.Quiver.Path j s |
          d.1.comp (a.toPath.comp d.2) = .nil} = ∅ :=
        Set.eq_empty_of_forall_notMem fun d hd => by
          simpa [_root_.Quiver.Path.length_comp] using
            congrArg _root_.Quiver.Path.length
              (show d.1.comp (a.toPath.comp d.2) = .nil from hd)
      rw [cyclicDerivativePath_nil, hempty, finsum_mem_empty]
  | @cons m t p e ih =>
      -- The decompositions of `p.cons e` with `u` nonempty are those of `p` followed by `e`; the
      -- one with `u` empty exists exactly when `e` is `a`.
      rw [cyclicDerivativePath_cons, ih, ← finsum_mem_inter_add_sdiff {d | d.2.length = 0}
        (finite_setOf_comp_toPath_comp_eq a (p.cons e))]
      have hdiff : {d : _root_.Quiver.Path s i × _root_.Quiver.Path j t |
            d.1.comp (a.toPath.comp d.2) = p.cons e} \ {d | d.2.length = 0} =
          (fun d => (d.1, d.2.cons e)) ''
            {d : _root_.Quiver.Path s i × _root_.Quiver.Path j m |
              d.1.comp (a.toPath.comp d.2) = p} := by
        ext ⟨v, u⟩
        constructor
        · rintro ⟨hd, hu⟩
          cases u with
          | nil => exact absurd rfl hu
          | cons u e' =>
              have hd : (v.comp (a.toPath.comp u)).cons e' = p.cons e := hd
              obtain rfl := _root_.Quiver.Path.obj_eq_of_cons_eq_cons hd
              obtain rfl := eq_of_heq (_root_.Quiver.Path.heq_of_cons_eq_cons hd)
              obtain rfl := eq_of_heq (_root_.Quiver.Path.hom_heq_of_cons_eq_cons hd)
              exact ⟨(v, u), rfl, rfl⟩
        · rintro ⟨⟨v', u'⟩, hd, h⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          refine ⟨?_, by simp⟩
          change (v'.comp (a.toPath.comp u')).cons e = p.cons e
          rw [show v'.comp (a.toPath.comp u') = p from hd]
      have hinj : Set.InjOn (fun d : _root_.Quiver.Path s i × _root_.Quiver.Path j m =>
          (d.1, d.2.cons e)) {d | d.1.comp (a.toPath.comp d.2) = p} := by
        rintro ⟨v, u⟩ - ⟨v', u'⟩ - h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        rw [eq_of_heq (_root_.Quiver.Path.heq_of_cons_eq_cons h)]
      rw [hdiff, finsum_mem_image hinj]
      congr 1
      · split_ifs with h
        · cases h
          have hsingle : {d : _root_.Quiver.Path s i × _root_.Quiver.Path j j |
                d.1.comp (a.toPath.comp d.2) = p.cons a} ∩ {d | d.2.length = 0} =
              {(p, _root_.Quiver.Path.nil)} := by
            ext ⟨v, u⟩
            constructor
            · rintro ⟨hd, hu⟩
              cases u with
              | nil =>
                  have hd : v.cons a = p.cons a := hd
                  rw [eq_of_heq (_root_.Quiver.Path.heq_of_cons_eq_cons hd)]
                  rfl
              | cons u e' => simp at hu
            · intro h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              exact ⟨rfl, rfl⟩
          rw [hsingle, finsum_mem_singleton, vertexIdempotent_eq_ofPath]
        · symm
          convert finsum_mem_empty
          refine Set.eq_empty_of_forall_notMem ?_
          rintro ⟨v, u⟩ ⟨hd, hu⟩
          cases u with
          | nil =>
              have hd : v.cons a = p.cons e := hd
              obtain rfl := _root_.Quiver.Path.obj_eq_of_cons_eq_cons hd
              obtain rfl := eq_of_heq (_root_.Quiver.Path.hom_heq_of_cons_eq_cons hd)
              exact h rfl
          | cons u e' => simp at hu
      · refine finsum_mem_congr rfl fun d _ => ?_
        rw [← ofArrow_mul_ofPath, mul_assoc, mul_assoc, mul_assoc]

end Path

section Derivative

variable (k : Type w) [CommSemiring k] {Q : Type u} [Quiver.{v} Q] [Finite Q]

/-- **The cyclic derivative** `∂_a` with respect to an arrow `a : i ⟶ j`. On a cycle which
traverses a path `v`, then `a`, then a path `u`, each such occurrence of `a` contributes the path
`u` followed by `v`, which is `ofPath v * ofPath u` in the later-factor-first convention; paths
which are not cycles have cyclic derivative `0`. -/
noncomputable def cyclicDerivative {i j : Q} (a : i ⟶ j) :
    pathAlgebra k Q →ₗ[k] pathAlgebra k Q :=
  liftLinear k fun x => cyclicDerivativePath k a x.2.2 1

variable {k} {i j : Q} (a : i ⟶ j)

private theorem cyclicDerivative_ofPath_eq (x : Quiver.TotalPath Q) :
    cyclicDerivative k a (ofPath x) = cyclicDerivativePath k a x.2.2 1 :=
  liftLinear_ofPath k _ x

/-- **The cyclic derivative with respect to `a : i ⟶ j` lies in the left corner of `i`.** -/
@[simp]
theorem vertexIdempotent_mul_cyclicDerivative (z : pathAlgebra k Q) :
    vertexIdempotent k i * cyclicDerivative k a z = cyclicDerivative k a z := by
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂]
  | single x r =>
      rw [single_eq_smul_ofPath, map_smul, mul_smul_comm, cyclicDerivative_ofPath_eq,
        vertexIdempotent_mul_cyclicDerivativePath]

/-- **The cyclic derivative with respect to `a : i ⟶ j` lies in the right corner of `j`.** -/
@[simp]
theorem cyclicDerivative_mul_vertexIdempotent (z : pathAlgebra k Q) :
    cyclicDerivative k a z * vertexIdempotent k j = cyclicDerivative k a z := by
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂]
  | single x r =>
      rw [single_eq_smul_ofPath, map_smul, smul_mul_assoc, cyclicDerivative_ofPath_eq,
        cyclicDerivativePath_mul_vertexIdempotent]

/-- **A path which is not a cycle has cyclic derivative `0`.** -/
@[simp]
theorem cyclicDerivative_ofPath_of_ne {s t : Q} (p : _root_.Quiver.Path s t) (h : s ≠ t) :
    cyclicDerivative k a (ofPath ⟨s, t, p⟩) = 0 := by
  rw [cyclicDerivative_ofPath_eq, ← cyclicDerivativePath_vertexIdempotent_mul,
    ← cyclicDerivativePath_mul_vertexIdempotent_right, mul_one,
    vertexIdempotent_mul_vertexIdempotent_of_ne h, cyclicDerivativePath_zero]

/-- **The cyclic derivative of a cycle**: the cyclic derivative with respect to `a : i ⟶ j` of a
cycle `c` is the sum, over the ways of writing `c` as a path `v`, then `a`, then a path `u`, of the
rotated remainder, the path traversing `u` and then `v`. -/
theorem cyclicDerivative_ofPath {s : Q} (c : _root_.Quiver.Path s s) :
    cyclicDerivative k a (ofPath ⟨s, s, c⟩) =
      ∑ᶠ d ∈ {d : _root_.Quiver.Path s i × _root_.Quiver.Path j s |
        d.1.comp (a.toPath.comp d.2) = c}, ofPath ⟨j, i, d.2.comp d.1⟩ := by
  rw [cyclicDerivative_ofPath_eq, cyclicDerivativePath_eq_finsum]
  exact finsum_mem_congr rfl fun d _ => by rw [mul_one, ofPath_mul_ofPath_of_comp]

/-- The cyclic derivative kills the vertex idempotents, which are paths of length `0`. -/
@[simp]
theorem cyclicDerivative_vertexIdempotent (v : Q) :
    cyclicDerivative k a (vertexIdempotent k v) = 0 := by
  rw [vertexIdempotent_eq_ofPath, cyclicDerivative_ofPath_eq, cyclicDerivativePath_nil]

/-- The cyclic derivative of a loop with respect to itself is the vertex idempotent at its
vertex. -/
theorem cyclicDerivative_ofArrow_self (a : i ⟶ i) :
    cyclicDerivative k a (ofArrow a) = vertexIdempotent k i := by
  classical
  rw [ofArrow_eq_ofPath, cyclicDerivative_ofPath_eq, Quiver.Hom.toPath, cyclicDerivativePath_cons,
    cyclicDerivativePath_nil, ite_eq_left rfl, add_zero, ← vertexIdempotent_eq_ofPath, mul_one,
    vertexIdempotent_mul_self]

/-- The cyclic derivative of an arrow with respect to a different arrow vanishes. -/
theorem cyclicDerivative_ofArrow_of_ne {m t : Q} (b : m ⟶ t)
    (h : (⟨m, t, b⟩ : Σ x z : Q, x ⟶ z) ≠ ⟨i, j, a⟩) :
    cyclicDerivative k a (ofArrow b) = 0 := by
  classical
  rw [ofArrow_eq_ofPath, cyclicDerivative_ofPath_eq, Quiver.Hom.toPath, cyclicDerivativePath_cons,
    cyclicDerivativePath_nil, ite_eq_right h, add_zero]

/-- The cyclic derivative of a product of two basis paths does not depend on their order. -/
private theorem cyclicDerivative_ofPath_mul_ofPath_comm (x y : Quiver.TotalPath Q) :
    cyclicDerivative k a (ofPath x * ofPath y) = cyclicDerivative k a (ofPath y * ofPath x) := by
  obtain ⟨t, s', q⟩ := x
  obtain ⟨s, t', p⟩ := y
  rcases eq_or_ne t' t with rfl | ht
  · rcases eq_or_ne s' s with rfl | hs
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp, cyclicDerivative_ofPath_eq,
        cyclicDerivative_ofPath_eq, cyclicDerivativePath_comp, cyclicDerivativePath_comp, mul_one,
        one_mul, mul_one, one_mul, add_comm]
    · rw [ofPath_mul_ofPath_of_comp, cyclicDerivative_ofPath_of_ne _ _ hs.symm,
        ofPath_mul_ofPath_of_not_composable hs, map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable ht, map_zero]
    rcases eq_or_ne s' s with rfl | hs
    · rw [ofPath_mul_ofPath_of_comp, cyclicDerivative_ofPath_of_ne _ _ ht.symm]
    · rw [ofPath_mul_ofPath_of_not_composable hs, map_zero]

/-- **The cyclic derivative is invariant under cyclic permutation**: it takes the same value on
`x * y` and on `y * x`, so that it vanishes on commutators and only depends on a potential up to
cyclic equivalence. -/
theorem cyclicDerivative_mul_comm (x y : pathAlgebra k Q) :
    cyclicDerivative k a (x * y) = cyclicDerivative k a (y * x) := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, mul_add, map_add, map_add, h₁, h₂]
  | single x r =>
      induction y using induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => rw [add_mul, mul_add, map_add, map_add, h₁, h₂]
      | single y c =>
          rw [single_eq_smul_ofPath, single_eq_smul_ofPath, smul_mul_smul_comm,
            smul_mul_smul_comm, map_smul, map_smul, cyclicDerivative_ofPath_mul_ofPath_comm,
            mul_comm r c]

end Derivative

section CyclicIdentity

variable {k : Type w} [CommSemiring k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

open scoped Classical in
/-- Summing over the arrows into `v` picks out the arrow `e` exactly when `e` ends at `v`. -/
private theorem sum_sum_ofArrow_mul_ite {m t : Q} (e : m ⟶ t) (v : Q) (y : pathAlgebra k Q) :
    ∑ i : Q, ∑ a : i ⟶ v, ofArrow a *
        (if (⟨m, t, e⟩ : Σ x z : Q, x ⟶ z) = ⟨i, v, a⟩ then y * vertexIdempotent k v else 0) =
      ofArrow e * y * vertexIdempotent k t * vertexIdempotent k v := by
  rcases eq_or_ne t v with rfl | htv
  · rw [Fintype.sum_eq_single m, Fintype.sum_eq_single e, ite_eq_left rfl]
    · simp only [mul_assoc, vertexIdempotent_mul_self]
    · intro b hb
      rw [ite_eq_right (by simpa [eq_comm] using hb), mul_zero]
    · intro i hi
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (fun h => hi (congrArg Sigma.fst h).symm), mul_zero]
  · rw [mul_assoc _ (vertexIdempotent k t), vertexIdempotent_mul_vertexIdempotent_of_ne htv,
      mul_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (fun h => htv (congrArg (fun x => x.2.1) h)), mul_zero]

open scoped Classical in
/-- Summing over the arrows out of `v` picks out the arrow `e` exactly when `e` starts at `v`. -/
private theorem sum_sum_ite_mul_ofArrow {m t : Q} (e : m ⟶ t) (v : Q) (y : pathAlgebra k Q) :
    ∑ j : Q, ∑ a : v ⟶ j,
        (if (⟨m, t, e⟩ : Σ x z : Q, x ⟶ z) = ⟨v, j, a⟩ then y * vertexIdempotent k j else 0) *
          ofArrow a =
      y * ofArrow e * vertexIdempotent k v := by
  rcases eq_or_ne m v with rfl | hmv
  · rw [Fintype.sum_eq_single t, Fintype.sum_eq_single e, ite_eq_left rfl, mul_assoc, mul_assoc,
      ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent]
    · intro b hb
      rw [ite_eq_right (by simpa [eq_comm] using hb), zero_mul]
    · intro j hj
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (fun h => hj (congrArg (fun x => x.2.1) h).symm), zero_mul]
  · rw [mul_assoc, ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm hmv), mul_zero]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (fun h => hmv (congrArg Sigma.fst h)), zero_mul]

/-- The telescoping identity behind the cyclic identity, for a path `p` from `s` to `t` and an
arbitrary accumulator `y`. -/
private theorem sum_ofArrow_mul_cyclicDerivativePath (v : Q) {s t : Q}
    (p : _root_.Quiver.Path s t) (y : pathAlgebra k Q) :
    (∑ i : Q, ∑ a : i ⟶ v, ofArrow a * cyclicDerivativePath k a p y) +
        vertexIdempotent k v * vertexIdempotent k s * y * ofPath ⟨s, t, p⟩ =
      (∑ j : Q, ∑ a : v ⟶ j, cyclicDerivativePath k a p y * ofArrow a) +
        ofPath ⟨s, t, p⟩ * y * vertexIdempotent k t * vertexIdempotent k v := by
  classical
  induction p generalizing y with
  | nil =>
      simp only [cyclicDerivativePath_nil, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
        ← vertexIdempotent_eq_ofPath]
      rcases eq_or_ne v s with rfl | hvs
      · simp only [vertexIdempotent_mul_self, mul_assoc]
      · simp [vertexIdempotent_mul_vertexIdempotent_of_ne hvs,
          vertexIdempotent_mul_vertexIdempotent_of_ne hvs.symm, mul_assoc]
  | @cons m t p e ih =>
      simp only [cyclicDerivativePath_cons, mul_add, add_mul, Finset.sum_add_distrib,
        sum_sum_ofArrow_mul_ite, sum_sum_ite_mul_ofArrow]
      rw [← ofArrow_mul_ofPath]
      -- The induction hypothesis for the accumulator `y * e` accounts for the old terms of the
      -- sums; the new term of each sum is the new boundary term on the other side.
      have he : ofArrow e * vertexIdempotent k m = (ofArrow e : pathAlgebra k Q) := by
        rw [ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent]
      have key : ofPath ⟨s, m, p⟩ * (y * ofArrow e) * vertexIdempotent k m =
          ofPath ⟨s, m, p⟩ * y * ofArrow e := by
        rw [mul_assoc _ _ (vertexIdempotent k m), mul_assoc y, he, ← mul_assoc]
      have ih := ih (y * ofArrow e)
      rw [key] at ih
      simp only [mul_assoc] at ih ⊢
      rw [add_assoc, ih]
      abel

/-- **The local cyclic identity**: at every vertex `v`, the arrows `a` with head `v` and those
with tail `v` give `∑_{head a = v} a ∂_a(x) = ∑_{tail a = v} ∂_a(x) a`. -/
theorem sum_ofArrow_mul_cyclicDerivative_eq_sum_cyclicDerivative_mul_ofArrow
    (x : pathAlgebra k Q) (v : Q) :
    ∑ i : Q, ∑ a : i ⟶ v, ofArrow a * cyclicDerivative k a x =
      ∑ j : Q, ∑ a : v ⟶ j, cyclicDerivative k a x * ofArrow a := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | single x r =>
      simp only [single_eq_smul_ofPath, map_smul, mul_smul_comm, smul_mul_assoc,
        ← Finset.smul_sum]
      congr 1
      obtain ⟨s, t, p⟩ := x
      cases p with
      | nil =>
          simp only [cyclicDerivative_ofPath_eq, cyclicDerivativePath_nil, mul_zero, zero_mul,
            Finset.sum_const_zero]
      | @cons m _ q e =>
          rcases eq_or_ne s t with rfl | hst
          · -- The new terms contributed by the last arrow `e` of the cycle are the two boundary
            -- terms of the telescoping identity along `q` with accumulator `e`.
            simp only [cyclicDerivative_ofPath_eq, cyclicDerivativePath_cons, mul_add, add_mul,
              Finset.sum_add_distrib, sum_sum_ofArrow_mul_ite, sum_sum_ite_mul_ofArrow, one_mul,
              mul_one]
            have h := sum_ofArrow_mul_cyclicDerivativePath (k := k) v q (ofArrow e)
            have hl : vertexIdempotent k v *
                  (vertexIdempotent k s * (ofArrow e * ofPath ⟨s, m, q⟩)) =
                ofArrow e * (ofPath ⟨s, m, q⟩ * (vertexIdempotent k s * vertexIdempotent k v)) := by
              rw [ofArrow_mul_ofPath, vertexIdempotent_mul_ofPath, ← mul_assoc (ofArrow e),
                ofArrow_mul_ofPath, ← mul_assoc, ofPath_mul_vertexIdempotent]
              rcases eq_or_ne v s with rfl | hvs
              · rw [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent]
              · rw [vertexIdempotent_mul_ofPath_of_ne _ hvs,
                  ofPath_mul_vertexIdempotent_of_ne _ hvs]
            have hr : ofPath ⟨s, m, q⟩ *
                  (ofArrow e * (vertexIdempotent k m * vertexIdempotent k v)) =
                ofPath ⟨s, m, q⟩ * (ofArrow e * vertexIdempotent k v) := by
              rw [← mul_assoc (ofArrow e), ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent]
            simp only [mul_assoc] at h ⊢
            rw [hl, hr] at h
            exact (add_comm _ _).trans (h.trans (add_comm _ _))
          · simp only [cyclicDerivative_ofPath_of_ne _ _ hst, mul_zero, zero_mul,
              Finset.sum_const_zero]

/-- **The global cyclic identity** `∑_a a ∂_a(x) = ∑_a ∂_a(x) a`, the sums running over all arrows
of `Q`. -/
theorem sum_sum_sum_ofArrow_mul_cyclicDerivative_comm (x : pathAlgebra k Q) :
    ∑ i : Q, ∑ j : Q, ∑ a : i ⟶ j, ofArrow a * cyclicDerivative k a x =
      ∑ i : Q, ∑ j : Q, ∑ a : i ⟶ j, cyclicDerivative k a x * ofArrow a := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ =>
    sum_ofArrow_mul_cyclicDerivative_eq_sum_cyclicDerivative_mul_ofArrow x v

end CyclicIdentity

end PathAlgebra

end TauCeti
