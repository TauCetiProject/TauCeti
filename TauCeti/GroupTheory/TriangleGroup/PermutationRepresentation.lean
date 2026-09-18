/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import TauCeti.GroupTheory.TriangleGroup.Basic

/-!
# Permutation triples as permutation representations of triangle groups

A permutation triple `t` of degree `n` whose components satisfy `t.σ0 ^ a = 1`, `t.σ1 ^ b = 1`
and `t.σinf ^ c = 1` is the same thing as a homomorphism `Δ(a, b, c) →* Equiv.Perm (Fin n)`: the
product relation `σinf * σ1 * σ0 = 1` of the triple is the product relator `z * y * x` of the
triangle group, so the universal property `TauCeti.TriangleGroup.lift` sends `x, y, z` to
`σ0, σ1, σinf`. This file records that dictionary.

* `TauCeti.TriangleGroup.toPerm`: the permutation representation of `Δ(a, b, c)` attached to a
  triple whose component orders divide `a`, `b`, `c`. Its range is the monodromy group of the
  triple (`TauCeti.TriangleGroup.range_toPerm`), so the triple is connected exactly when the
  representation is transitive on a nonempty set of sheets
  (`TauCeti.TriangleGroup.isConnected_iff_isPretransitive_range_toPerm`).
* `TauCeti.TriangleGroup.permutationTripleEquiv`: every permutation representation of
  `Δ(a, b, c)` on `Fin n` arises in this way from exactly one such triple.
* Relabeling the sheets of a triple conjugates its representation
  (`TauCeti.TriangleGroup.toPerm_smul`), and two representations give isomorphic triples exactly
  when they are conjugate (`TauCeti.TriangleGroup.equivalent_permutationTripleEquiv_iff`).
  Together with the connectedness criterion, isomorphism classes of connected triples with
  component orders dividing `(a, b, c)` therefore correspond to conjugacy classes of transitive
  permutation representations of `Δ(a, b, c)` of degree `n ≠ 0`.
* `TauCeti.TriangleGroup.isConnected_permutationTripleEquiv_toPermHom_iff`: the same criterion
  phrased for an action of `Δ(a, b, c)` on `Fin n`: the triple of the action is connected exactly
  when the action is pretransitive and `n ≠ 0`.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §4.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.5.
-/

open Equiv

public section

namespace TauCeti

namespace TriangleGroup

variable {a b c n : ℕ}

/-! ### The representation of a triple -/

/-- The permutation representation of `Δ(a, b, c)` on the sheets of a permutation triple whose
components have orders dividing `a`, `b`, `c`: it sends `x, y, z` to `σ0, σ1, σinf`. -/
def toPerm (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
    (hc : t.σinf ^ c = 1) : TriangleGroup a b c →* Perm (Fin n) :=
  lift t.σ0 t.σ1 t.σinf ha hb hc t.product_eq_one

section toPerm

variable (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
  (hc : t.σinf ^ c = 1)

@[simp]
theorem toPerm_x : toPerm t ha hb hc (x a b c) = t.σ0 :=
  lift_x ..

@[simp]
theorem toPerm_y : toPerm t ha hb hc (y a b c) = t.σ1 :=
  lift_y ..

@[simp]
theorem toPerm_z : toPerm t ha hb hc (z a b c) = t.σinf :=
  lift_z ..

/-- The image of the permutation representation of a triple is its monodromy group. -/
@[simp]
theorem range_toPerm : (toPerm t ha hb hc).range = t.monodromyGroup := by
  rw [range_eq_closure, toPerm_x, toPerm_y, PermutationTriple.closure_pair_eq_monodromyGroup]

/-- A triple is connected exactly when it has a sheet and its permutation representation of the
triangle group is transitive on the sheets. -/
theorem isConnected_iff_isPretransitive_range_toPerm :
    t.IsConnected ↔ n ≠ 0 ∧ MulAction.IsPretransitive (toPerm t ha hb hc).range (Fin n) := by
  rw [range_toPerm, PermutationTriple.isConnected_iff]

/-- Relabeling the sheets of a triple by `τ` conjugates its permutation representation by `τ`. -/
theorem toPerm_smul (τ : Perm (Fin n)) (ha' : (τ • t).σ0 ^ a = 1) (hb' : (τ • t).σ1 ^ b = 1)
    (hc' : (τ • t).σinf ^ c = 1) :
    toPerm (τ • t) ha' hb' hc' = (MulAut.conj τ).toMonoidHom.comp (toPerm t ha hb hc) := by
  ext <;> simp

end toPerm

/-! ### Every representation comes from a triple -/

/-- Permutation representations of `Δ(a, b, c)` on `Fin n` correspond to permutation triples of
degree `n` whose components have orders dividing `a`, `b`, `c`: a representation `ρ` gives the
triple `(ρ x, ρ y, ρ z)`, and the inverse is `TauCeti.TriangleGroup.toPerm`. -/
def permutationTripleEquiv :
    (TriangleGroup a b c →* Perm (Fin n)) ≃
      {t : PermutationTriple n // t.σ0 ^ a = 1 ∧ t.σ1 ^ b = 1 ∧ t.σinf ^ c = 1} where
  toFun ρ :=
    ⟨⟨ρ (x a b c), ρ (y a b c), ρ (z a b c), by rw [← map_mul, ← map_mul, z_mul_y_mul_x, map_one]⟩,
      by simp only [← map_pow, x_pow, y_pow, z_pow, map_one, and_self]⟩
  invFun t := toPerm t.1 t.2.1 t.2.2.1 t.2.2.2
  left_inv ρ := by ext <;> simp
  right_inv t := by ext1; ext1 <;> simp

section permutationTripleEquiv

variable (ρ : TriangleGroup a b c →* Perm (Fin n))

@[simp]
theorem permutationTripleEquiv_apply_σ0 : (permutationTripleEquiv ρ).1.σ0 = ρ (x a b c) := (rfl)

@[simp]
theorem permutationTripleEquiv_apply_σ1 : (permutationTripleEquiv ρ).1.σ1 = ρ (y a b c) := (rfl)

@[simp]
theorem permutationTripleEquiv_apply_σinf :
    (permutationTripleEquiv ρ).1.σinf = ρ (z a b c) := (rfl)

@[simp]
theorem permutationTripleEquiv_symm_apply
    (t : {t : PermutationTriple n // t.σ0 ^ a = 1 ∧ t.σ1 ^ b = 1 ∧ t.σinf ^ c = 1}) :
    permutationTripleEquiv.symm t = toPerm t.1 t.2.1 t.2.2.1 t.2.2.2 := (rfl)

/-- The permutation representation of the triple of `ρ` is `ρ` itself. -/
@[simp]
theorem toPerm_permutationTripleEquiv {ha hb hc} :
    toPerm (permutationTripleEquiv ρ).1 ha hb hc = ρ :=
  permutationTripleEquiv.symm_apply_apply ρ

/-- The monodromy group of the triple of a representation is the image of the representation. -/
@[simp]
theorem monodromyGroup_permutationTripleEquiv :
    (permutationTripleEquiv ρ).1.monodromyGroup = ρ.range := by
  rw [← range_toPerm _ (permutationTripleEquiv ρ).2.1 (permutationTripleEquiv ρ).2.2.1
    (permutationTripleEquiv ρ).2.2.2, toPerm_permutationTripleEquiv]

/-- The triple of a representation is connected exactly when the representation is transitive on
a nonempty set of sheets. -/
theorem isConnected_permutationTripleEquiv_iff :
    (permutationTripleEquiv ρ).1.IsConnected ↔
      n ≠ 0 ∧ MulAction.IsPretransitive ρ.range (Fin n) := by
  rw [PermutationTriple.isConnected_iff, monodromyGroup_permutationTripleEquiv]

/-- Conjugating a representation by `τ` relabels the sheets of its triple by `τ`. -/
@[simp]
theorem permutationTripleEquiv_conj (τ : Perm (Fin n)) :
    (permutationTripleEquiv
      ((↑(MulAut.conj τ) : Perm (Fin n) →* Perm (Fin n)).comp ρ)).1 =
      τ • (permutationTripleEquiv ρ).1 := by
  ext1 <;> simp

/-- **Classification up to relabeling.** Two permutation representations of `Δ(a, b, c)` give
isomorphic triples exactly when they are conjugate by a permutation of the sheets. -/
theorem equivalent_permutationTripleEquiv_iff (ρ' : TriangleGroup a b c →* Perm (Fin n)) :
    PermutationTriple.Equivalent (permutationTripleEquiv ρ).1 (permutationTripleEquiv ρ').1 ↔
      ∃ τ : Perm (Fin n),
        ((↑(MulAut.conj τ) : Perm (Fin n) →* Perm (Fin n)).comp ρ) = ρ' := by
  rw [PermutationTriple.equivalent_iff_exists_smul_eq]
  refine exists_congr fun τ ↦ ?_
  rw [← permutationTripleEquiv_conj, ← Subtype.ext_iff, permutationTripleEquiv.apply_eq_iff_eq]

end permutationTripleEquiv

/-! ### Actions of the triangle group -/

/-- An action of `Δ(a, b, c)` on the `n` sheets gives a connected triple exactly when the action is
pretransitive and there is at least one sheet. -/
theorem isConnected_permutationTripleEquiv_toPermHom_iff
    [MulAction (TriangleGroup a b c) (Fin n)] :
    (permutationTripleEquiv (MulAction.toPermHom (TriangleGroup a b c) (Fin n))).1.IsConnected ↔
      n ≠ 0 ∧ MulAction.IsPretransitive (TriangleGroup a b c) (Fin n) := by
  rw [isConnected_permutationTripleEquiv_iff]
  refine and_congr_right fun _ ↦ ⟨fun ⟨h⟩ ↦ ⟨fun i j ↦ ?_⟩, fun ⟨h⟩ ↦ ⟨fun i j ↦ ?_⟩⟩
  · obtain ⟨⟨_, g, rfl⟩, hg⟩ := h i j
    exact ⟨g, hg⟩
  · obtain ⟨g, hg⟩ := h i j
    exact ⟨⟨_, g, rfl⟩, hg⟩

end TriangleGroup

end TauCeti
