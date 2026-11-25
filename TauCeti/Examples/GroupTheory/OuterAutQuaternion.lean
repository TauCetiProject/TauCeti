/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.GroupTheory.Automorphism.Outer
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Discrete

import Mathlib.Data.Finite.Perm
import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# The outer automorphism group of the quaternion group

The orders of `TauCeti.OuterAut` and `TauCeti.ContinuousOut` for the quaternion group
`Q₈ = QuaternionGroup 2`: `MulAut Q₈` has order `24`, the centre has order `2`, so the inner
automorphisms, a quotient of `Q₈` by its centre, form a group of order `4`, and `OuterAut Q₈` has
order `6`; with the discrete topology `ContinuousOut Q₈` has order `6` too. Moreover
`MulAut Q₈ ≅ S₄` (`nonempty_mulEquiv_perm`), by the action on the four body diagonals of the cube
whose six faces are the elements of order `4`.

An automorphism `φ` of `Q₈` is determined by the pair `(φ(a 1), φ(xa 0))`, since
`a i = (a 1) ^ i` and `xa i = xa 0 * (a 1) ^ i`. Conversely a pair `(u, v)` comes from an
automorphism exactly when `a i ↦ u ^ i`, `xa i ↦ v * u ^ i` is an injective homomorphism, which
is decidable; there are `24` such pairs.
-/

public section

open QuaternionGroup

namespace TauCeti.QuaternionOuterAut

/-- The quaternion group `Q₈`. -/
local notation "Q₈" => QuaternionGroup 2

/-- The map `a i ↦ u ^ i`, `xa i ↦ v * u ^ i` attached to a pair `p = (u, v)`. -/
private def ofGens (p : Q₈ × Q₈) : Q₈ → Q₈
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

/-- The pairs `(u, v)` for which `ofGens (u, v)` is an injective homomorphism. -/
private def IsGenPair (p : Q₈ × Q₈) : Prop :=
  (∀ x y, ofGens p (x * y) = ofGens p x * ofGens p y) ∧ Function.Injective (ofGens p)

private instance : DecidablePred IsGenPair := fun _ => by unfold IsGenPair; infer_instance

/-- Exactly `24` pairs satisfy `IsGenPair`. -/
private theorem card_isGenPair : Fintype.card {p : Q₈ × Q₈ // IsGenPair p} = 24 := by
  decide +kernel

/-- An automorphism `φ` of `Q₈` agrees with `ofGens` of its values on `a 1` and `xa 0`. -/
private theorem ofGens_apply_eq (φ : MulAut Q₈) (x : Q₈) : ofGens (φ (a 1), φ (xa 0)) x = φ x := by
  cases x with
  | a i => simp [ofGens, ← map_pow, a_one_pow]
  | xa i => simp [ofGens, ← map_pow, ← map_mul, a_one_pow, xa_mul_a]

/-- The images of `a 1` and `xa 0` under an automorphism form a pair satisfying `IsGenPair`. -/
private theorem isGenPair_mulAut (φ : MulAut Q₈) : IsGenPair (φ (a 1), φ (xa 0)) := by
  have h : ofGens (φ (a 1), φ (xa 0)) = φ := funext (ofGens_apply_eq φ)
  refine ⟨fun x y => ?_, ?_⟩ <;> rw [h]
  · exact map_mul φ x y
  · exact φ.injective

/-- The automorphism of `Q₈` attached to a pair satisfying `IsGenPair`. -/
private noncomputable def mulAutOfIsGenPair (p : {p : Q₈ × Q₈ // IsGenPair p}) : MulAut Q₈ :=
  MulEquiv.ofBijective (MulHom.mk (ofGens p.val) p.property.1)
    (Finite.injective_iff_bijective.1 p.property.2)

private theorem mulAutOfIsGenPair_apply (p : {p : Q₈ × Q₈ // IsGenPair p}) (x : Q₈) :
    mulAutOfIsGenPair p x = ofGens p.val x :=
  rfl

/-- `MulAut Q₈` is in bijection with the pairs satisfying `IsGenPair`, by
`φ ↦ (φ(a 1), φ(xa 0))`. -/
private noncomputable def mulAutEquiv : MulAut Q₈ ≃ {p : Q₈ × Q₈ // IsGenPair p} where
  toFun φ := ⟨(φ (a 1), φ (xa 0)), isGenPair_mulAut φ⟩
  invFun := mulAutOfIsGenPair
  left_inv φ := MulEquiv.ext fun x => by
    rw [mulAutOfIsGenPair_apply, ofGens_apply_eq]
  right_inv p := by
    obtain ⟨⟨u, v⟩, hp⟩ := p
    have h1 : (1 : ZMod (2 * 2)).val = 1 := by decide
    ext <;> simp [mulAutOfIsGenPair_apply, ofGens, h1]

/-- `MulAut Q₈` has order `24`. -/
theorem card_mulAut : Nat.card (MulAut Q₈) = 24 := by
  rw [Nat.card_congr mulAutEquiv, Nat.card_eq_fintype_card, card_isGenPair]

/-! ### `MulAut Q₈ ≅ S₄`

The elements of order `4` of `Q₈` are `±a 1`, `±xa 0`, `±xa 1`, the six faces of a cube, with
`-1 = a 2`. A vertex is a triple of faces `{u, v, w}`, one from each pair, and a body diagonal is a
pair of opposite vertices `{S, -S}`; there are four. An automorphism permutes the faces and
commutes with `x ↦ -x`, so it permutes the diagonals, and the only automorphism fixing all four
is the identity. Each diagonal contains exactly one vertex through `a 1`, which indexes it. -/

/-- The vertex through `a 1` of the `d`-th body diagonal. -/
private def vertex : Fin 4 → Finset Q₈
  | 0 => {a 1, xa 0, xa 1}
  | 1 => {a 1, xa 0, xa 3}
  | 2 => {a 1, xa 2, xa 1}
  | 3 => {a 1, xa 2, xa 3}

/-- The body diagonal through a vertex `S`: the index of `S` or of `-S`, whichever contains
`a 1`. -/
private def diagonal (S : Finset Q₈) : Fin 4 :=
  let T := if a 1 ∈ S then S else S.image (a 2 * ·)
  if xa 0 ∈ T then (if xa 1 ∈ T then 0 else 1) else (if xa 1 ∈ T then 2 else 3)

/-- The eight vertices of the cube. -/
private def vertices : Finset (Finset Q₈) :=
  Finset.univ.image vertex ∪ Finset.univ.image fun d ↦ (vertex d).image (a 2 * ·)

/-- The images of the vertices under the map attached to a generating pair are vertices. -/
private theorem image_vertex_mem_vertices :
    ∀ p : {p : Q₈ × Q₈ // IsGenPair p}, ∀ d, (vertex d).image (ofGens p.val) ∈ vertices := by
  decide +kernel

/-- The map attached to a generating pair sends a vertex and its opposite to the same
diagonal. -/
private theorem diagonal_image_vertex_diagonal :
    ∀ p : {p : Q₈ × Q₈ // IsGenPair p}, ∀ S ∈ vertices,
      diagonal (S.image (ofGens p.val)) =
        diagonal ((vertex (diagonal S)).image (ofGens p.val)) := by
  decide +kernel

/-- Only the identity pair fixes all four diagonals. -/
private theorem eq_of_diagonal_image_vertex :
    ∀ p : {p : Q₈ × Q₈ // IsGenPair p},
      (∀ d, diagonal ((vertex d).image (ofGens p.val)) = d) → p.val = (a 1, xa 0) := by
  decide +kernel

private theorem diagonal_vertex : ∀ d, diagonal (vertex d) = d := by
  decide

/-- The map of an automorphism `φ` is `ofGens` of the pair `(φ(a 1), φ(xa 0))`. -/
private theorem coe_eq_ofGens (φ : MulAut Q₈) :
    ⇑φ = ofGens (φ (a 1), φ (xa 0)) :=
  (funext (ofGens_apply_eq φ)).symm

/-- The action of an automorphism on the four body diagonals. -/
private def diagonalMap (φ : MulAut Q₈) (d : Fin 4) : Fin 4 :=
  diagonal ((vertex d).image φ)

private theorem diagonalMap_mul (φ ψ : MulAut Q₈) (d : Fin 4) :
    diagonalMap (φ * ψ) d = diagonalMap φ (diagonalMap ψ d) := by
  have hψ : (vertex d).image ψ ∈ vertices := by
    rw [coe_eq_ofGens ψ]
    exact image_vertex_mem_vertices ⟨_, isGenPair_mulAut ψ⟩ d
  have h := diagonal_image_vertex_diagonal ⟨_, isGenPair_mulAut φ⟩ _ hψ
  rw [← coe_eq_ofGens φ] at h
  rw [diagonalMap, diagonalMap, diagonalMap, ← h, Finset.image_image, MulAut.coe_mul]

private theorem diagonalMap_one (d : Fin 4) : diagonalMap 1 d = d := by
  simp [diagonalMap, diagonal_vertex]

/-- The action of `MulAut Q₈` on the four body diagonals of the cube. -/
private def toPerm : MulAut Q₈ →* Equiv.Perm (Fin 4) :=
  MonoidHom.toHomPerm
    { toFun := diagonalMap
      map_one' := funext diagonalMap_one
      map_mul' φ ψ :=
        (funext fun d ↦ (diagonalMap_mul φ ψ d).trans Function.comp_apply.symm).trans
          (Function.End.mul_def (diagonalMap φ) (diagonalMap ψ)).symm }

/-- `toPerm` acts by `diagonalMap`. Mathlib has no `MonoidHom.toHomPerm_apply` lemma, so this
holds by unfolding `MonoidHom.toHomPerm`; later proofs use this lemma rather than the unfolding. -/
private theorem toPerm_apply (φ : MulAut Q₈) (d : Fin 4) : toPerm φ d = diagonalMap φ d :=
  rfl

private theorem toPerm_injective : Function.Injective toPerm := by
  refine (injective_iff_map_eq_one toPerm).2 fun φ hφ ↦ ?_
  have h := eq_of_diagonal_image_vertex ⟨_, isGenPair_mulAut φ⟩ fun d ↦ by
    rw [← coe_eq_ofGens φ]
    exact (toPerm_apply φ d).symm.trans (DFunLike.congr_fun hφ d)
  exact mulAutEquiv.injective (Subtype.ext h)

/-- **`MulAut Q₈ ≅ S₄`**: the automorphism group of the quaternion group is isomorphic to the
symmetric group on four letters. -/
theorem nonempty_mulEquiv_perm : Nonempty (MulAut Q₈ ≃* Equiv.Perm (Fin 4)) :=
  ⟨MulEquiv.ofBijective toPerm <| toPerm_injective.bijective_of_nat_card_le
    (by rw [card_mulAut, Nat.card_perm, Nat.card_fin]; decide)⟩

/-- The inner automorphisms of `Q₈` form a group of order `4 = |Q₈ / Z(Q₈)|`. -/
theorem card_range_conj : Nat.card (MulAut.conj : Q₈ →* MulAut Q₈).range = 4 := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MulAut.ker_conj,
    ← Subgroup.index_eq_card, index_center_quaternionGroup (by decide)]

/-- `OuterAut Q₈` has order `24 / 4 = 6`. -/
theorem card_outerAut : Nat.card (OuterAut Q₈) = 6 := by
  have h : Nat.card (MulAut Q₈) =
      Nat.card (OuterAut Q₈) * Nat.card (MulAut.conj : Q₈ →* MulAut Q₈).range :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_mulAut, card_range_conj] at h
  omega

section Discrete

/-- The discrete topology on `Q₈`. -/
local instance instTopologicalSpace : TopologicalSpace Q₈ := ⊥

local instance instDiscreteTopology : DiscreteTopology Q₈ := ⟨rfl⟩

/-- With the discrete topology, `ContinuousOut Q₈` has order `6`, agreeing with `OuterAut Q₈`. -/
theorem card_continuousOut : Nat.card (ContinuousOut Q₈) = 6 := by
  rw [Nat.card_congr ContinuousOut.mulEquivOuterAutOfDiscrete.toEquiv, card_outerAut]

end Discrete

end TauCeti.QuaternionOuterAut
