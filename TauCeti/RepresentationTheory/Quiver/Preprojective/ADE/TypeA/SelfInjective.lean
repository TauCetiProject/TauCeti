/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basis
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Multiplication

/-!
# Self-injectivity of the preprojective algebras of type `A`

Let `Π` be the signless preprojective algebra of the Bourbaki-labelled `Aₙ` diagram
`0 — 1 — ⋯ — (n - 1)`, and write `ν a = n - 1 - a` for the reflection of the diagram. In the
corner `e_{ν a} Π e_a` the bounded valleys have bottoms `0 ≤ m ≤ min a (ν a)`, and the valley
with bottom `0` is the unique one of the maximal length `n - 1`. The **Frobenius functional**
`TauCeti.signlessPreprojectiveAFrobeniusFunctional` takes, on every corner `e_{ν a} Π e_a`, the
coefficient of that longest valley in the corner basis
`TauCeti.signlessPreprojectiveACornerBasis`, and vanishes on every other corner.

By the multiplication formula for valleys, the valley from `a` to `b` with bottom `m` and the
valley from `ν b` to `a` with bottom `a - m'` multiply to `± 1` times the longest valley of the
corner `e_b Π e_{ν b}` when `m = m'`, and otherwise to zero or to a multiple of a shorter valley.
Hence the bilinear form `(x, y) ↦ φ (x * y)` has a signed permutation matrix as Gram matrix in the
valley bases, and is nondegenerate over every field, characteristic two included.

Consequently the signless algebra of `Aₙ`, and the additive preprojective algebra `Π_k(Q)` of
every orientation `Q` of `Aₙ` (which is isomorphic to it by a sign rescaling of the arrows), is a
finite-dimensional Frobenius algebra, and in particular left and right self-injective.

## Main definitions

* `TauCeti.signlessPreprojectiveAFrobeniusFunctional`: the coefficient of the longest valley in
  the corners `e_{ν a} Π e_a`.

## Main results

* `TauCeti.signlessPreprojectiveAFrobeniusFunctional_valley`: the value of the functional on a
  bounded valley.
* `TauCeti.signlessPreprojectiveAFrobeniusFunctional_valley_mul_valley`: the pairing of two
  bounded valleys in complementary corners.
* `TauCeti.isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional`: it is a Frobenius
  functional.
* `TauCeti.moduleInjective_signlessPreprojectiveAlgebra_A` and
  `TauCeti.moduleInjective_op_signlessPreprojectiveAlgebra_A`: the signless algebra of `Aₙ` is
  left and right self-injective.
* `TauCeti.exists_isFrobeniusFunctional_preprojectiveAlgebra_A`,
  `TauCeti.moduleInjective_preprojectiveAlgebra_A` and
  `TauCeti.moduleInjective_op_preprojectiveAlgebra_A`: the preprojective algebra of every
  orientation of `Aₙ` is Frobenius, and left and right self-injective.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the Frobenius property of
  preprojective algebras of Dynkin quivers and their Nakayama permutation.
* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective relations.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [Field k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver AG)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver AG)
local notation "e" a:max => π (vertexIdempotent k (vertex AG a))

/-! ### Vertex idempotents and corners -/

private theorem isIdempotentElem_e (a : Fin (DynkinType.A n).rank) : IsIdempotentElem (e a) :=
  IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG a)) π

private theorem e_mul_e_of_ne {a b : Fin (DynkinType.A n).rank} (h : a ≠ b) : e a * e b = 0 := by
  classical
  rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne
    (fun hab => h (vertex_injective AG hab)), map_zero]

private theorem sum_e : ∑ a, e a = (1 : Π) := by
  rw [← map_one π, PathAlgebra.one_def, map_sum]
  exact Fintype.sum_equiv (vertexEquiv AG) _ (fun v => π (vertexIdempotent k v))
    fun a => by rw [vertexEquiv_apply]

/-- An element of the corner `e_b Π e_a` is killed by `e_c` on the right unless `c = a`. -/
private theorem mul_e_of_mem_corner {a b c : Fin (DynkinType.A n).rank} {x : Π}
    (hx : x ∈ cornerSubmodule k (e b) (e a)) (hc : c ≠ a) : x * e c = 0 := by
  rw [← mul_eq_self_of_mem_cornerSubmodule_right (isIdempotentElem_e k a) hx, mul_assoc,
    e_mul_e_of_ne k (Ne.symm hc), mul_zero]

private theorem cornerMap_mem (a b : Fin (DynkinType.A n).rank) (x : Π) :
    cornerMap k (e b) (e a) x ∈ cornerSubmodule k (e b) (e a) := by
  rw [mem_cornerSubmodule_iff k (isIdempotentElem_e k b) (isIdempotentElem_e k a),
    cornerMap_apply]
  simp only [← mul_assoc, (isIdempotentElem_e k b).eq]
  rw [mul_assoc _ (e a), (isIdempotentElem_e k a).eq]

/-- The coefficient of the valley with bottom `m` in the corner `e_b x e_a`. -/
private noncomputable def valleyCoord (a b : Fin (DynkinType.A n).rank)
    (m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))) : Π →ₗ[k] k :=
  ((signlessPreprojectiveACornerBasis k a b).coord m).comp
    ((cornerMap k (e b) (e a)).codRestrict _ (cornerMap_mem k a b))

private theorem valleyCoord_apply_of_mem (a b : Fin (DynkinType.A n).rank)
    (m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))) {x : Π}
    (hx : x ∈ cornerSubmodule k (e b) (e a)) :
    valleyCoord k a b m x = (signlessPreprojectiveACornerBasis k a b).repr ⟨x, hx⟩ m := by
  rw [valleyCoord, LinearMap.comp_apply, Module.Basis.coord_apply]
  congr 2
  rw [Subtype.ext_iff, LinearMap.codRestrict_apply, cornerMap_apply]
  exact (mem_cornerSubmodule_iff k (isIdempotentElem_e k b) (isIdempotentElem_e k a)).mp hx

private theorem valleyCoord_eq_zero (a b : Fin (DynkinType.A n).rank)
    (m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))) {x : Π}
    (hx : e b * x * e a = 0) : valleyCoord k a b m x = 0 := by
  rw [valleyCoord, LinearMap.comp_apply]
  convert map_zero ((signlessPreprojectiveACornerBasis k a b).coord m)
  rw [Subtype.ext_iff, LinearMap.codRestrict_apply, cornerMap_apply, hx, ZeroMemClass.coe_zero]

/-- The coordinate of a bounded valley in its own corner basis. -/
private theorem valleyCoord_valley (a b : Fin (DynkinType.A n).rank)
    (m l : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))) :
    valleyCoord k a b m (signlessPreprojectiveAValley k a b l) =
      if (l : ℕ) = m then 1 else 0 := by
  classical
  rw [valleyCoord_apply_of_mem k a b m (signlessPreprojectiveAValley_mem_cornerSubmodule k a b l)]
  have : (⟨signlessPreprojectiveAValley k a b l,
      signlessPreprojectiveAValley_mem_cornerSubmodule k a b l⟩ :
        cornerSubmodule k (e b) (e a)) = signlessPreprojectiveACornerBasis k a b l :=
    Subtype.ext (coe_signlessPreprojectiveACornerBasis_apply k a b l).symm
  rw [this, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr Subtype.ext_iff rfl rfl

/-- The longest valley of the corner `e_{ν a} Π e_a` has bottom `0`. -/
private theorem zero_mem_Icc_rev (a : Fin (DynkinType.A n).rank) :
    0 ∈ Finset.Icc (a.val + a.rev.val + 1 - n) (min a.val a.rev.val) := by
  have := a.isLt
  rw [Finset.mem_Icc, Fin.val_rev]
  simp only [DynkinType.rank_A] at this ⊢
  omega

/-! ### The Frobenius functional -/

/-- The **Frobenius functional** on the signless preprojective algebra of `Aₙ`: on each corner
`e_{ν a} Π e_a`, with `ν a = n - 1 - a`, it is the coefficient of the valley with bottom `0`, the
longest valley of that corner. It vanishes on every other corner. -/
noncomputable def signlessPreprojectiveAFrobeniusFunctional : Π →ₗ[k] k :=
  ∑ a, valleyCoord k a a.rev ⟨0, zero_mem_Icc_rev a⟩

/-- The functional vanishes on the corner `e_d Π e_c` unless `d = ν c`. -/
@[simp]
theorem signlessPreprojectiveAFrobeniusFunctional_mul_mul_eq_zero
    {c d : Fin (DynkinType.A n).rank} (h : d ≠ c.rev) (x : Π) :
    signlessPreprojectiveAFrobeniusFunctional k (e d * x * e c) = 0 := by
  rw [signlessPreprojectiveAFrobeniusFunctional, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun a _ => valleyCoord_eq_zero k _ _ _ ?_
  by_cases hac : a = c
  · subst hac
    rw [← mul_assoc, ← mul_assoc, e_mul_e_of_ne k (Ne.symm h), zero_mul, zero_mul, zero_mul]
  · simp only [mul_assoc]
    rw [e_mul_e_of_ne k (Ne.symm hac), mul_zero, mul_zero, mul_zero]

/-- **The Frobenius functional on bounded valleys**: it is `1` on the longest valley of each
corner `e_{ν a} Π e_a` and `0` on every other bounded valley. -/
@[simp]
theorem signlessPreprojectiveAFrobeniusFunctional_valley (a b : Fin (DynkinType.A n).rank) {m : ℕ}
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    signlessPreprojectiveAFrobeniusFunctional k (signlessPreprojectiveAValley k a b m) =
      if b = a.rev ∧ m = 0 then 1 else 0 := by
  have hmem : _ ∈ cornerSubmodule k (e b) (e a) :=
    signlessPreprojectiveAValley_mem_cornerSubmodule k a b m
  by_cases hb : b = a.rev
  · subst hb
    rw [signlessPreprojectiveAFrobeniusFunctional, LinearMap.sum_apply,
      Finset.sum_eq_single a]
    · simpa using valleyCoord_valley k a a.rev ⟨0, zero_mem_Icc_rev a⟩ ⟨m, hm⟩
    · intro c _ hca
      exact valleyCoord_eq_zero k _ _ _
        (by rw [mul_assoc, mul_e_of_mem_corner k hmem hca, mul_zero])
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [hb, false_and, ite_false]
    rw [← mul_eq_self_of_mem_cornerSubmodule_right
      (isIdempotentElem_e k a) hmem, ← mul_eq_self_of_mem_cornerSubmodule
      (isIdempotentElem_e k b) hmem]
    exact signlessPreprojectiveAFrobeniusFunctional_mul_mul_eq_zero k hb _

/-- **The Gram matrix in the valley bases**: the valley from `a` to `b` with bottom `l` pairs with
the valley from `ν b` to `a` with bottom `a - m` to a sign if `l = m`, and to zero otherwise. -/
theorem signlessPreprojectiveAFrobeniusFunctional_valley_mul_valley
    (a b : Fin (DynkinType.A n).rank) {l m : ℕ}
    (hl : l ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    signlessPreprojectiveAFrobeniusFunctional k (signlessPreprojectiveAValley k a b l *
        signlessPreprojectiveAValley k b.rev a (a.val - m)) =
      if l = m then (-1 : k) ^ ((a.val - m) * m) else 0 := by
  have hb := b.isLt
  have hrev := Fin.val_rev b
  have hn := DynkinType.rank_A n
  rw [Finset.mem_Icc] at hl hm
  by_cases hlm : l < m
  · rw [signlessPreprojectiveAValley_mul_eq_zero k b.rev a b (by omega), map_zero,
      ite_eq_right_iff.mpr fun h => absurd h hlm.ne]
  rw [signlessPreprojectiveAValley_mul k b.rev a b (by omega) (by omega) (by omega)]
  have hsign (N : ℕ) (v : Π) : (-1 : Π) ^ N * v = ((-1 : k) ^ N) • v := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  rw [hsign, map_smul, signlessPreprojectiveAFrobeniusFunctional_valley k b.rev b
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), Fin.rev_rev, smul_eq_mul]
  by_cases hml : l = m
  · subst hml
    simp only [true_and, ite_true, mul_one, show a.val - l + l - a.val = 0 by omega]
    congr 2
    omega
  · simp only [true_and, hml, show a.val - m + l - a.val ≠ 0 by omega, ite_false, mul_zero]

/-- **The Frobenius functional of the signless preprojective algebra of `Aₙ`.** The form
`(x, y) ↦ φ (x * y)` is nondegenerate over every field. -/
theorem isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional :
    (signlessPreprojectiveAFrobeniusFunctional k (n := n)).IsFrobeniusFunctional := by
  -- In finite dimension it suffices to separate on the left. Split `x` into its corners
  -- `e_b x e_a`, and test each corner against the valleys of the complementary corner.
  refine .of_left fun x hx => ?_
  have hsplit : x = ∑ a, ∑ b, e b * x * e a :=
    calc
      x = (∑ b, e b) * x * ∑ a, e a := by rw [sum_e, one_mul, mul_one]
      _ = ∑ a, ∑ b, e b * x * e a := by simp only [Finset.sum_mul, Finset.mul_sum]
  rw [hsplit]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have hz : e b * x * e a ∈ cornerSubmodule k (e b) (e a) := by
    simpa only [cornerMap_apply] using cornerMap_mem k a b x
  suffices h : (⟨_, hz⟩ : cornerSubmodule k (e b) (e a)) = 0 from congrArg Subtype.val h
  refine (signlessPreprojectiveACornerBasis k a b).ext_elem fun m => ?_
  rw [map_zero, Finsupp.zero_apply]
  -- Pair against the valley from `ν b` to `a` with bottom `a - m`.
  set y := signlessPreprojectiveAValley k b.rev a (a.val - m.val) with hy_def
  have hy : y ∈ cornerSubmodule k (e a) (e b.rev) :=
    signlessPreprojectiveAValley_mem_cornerSubmodule k b.rev a _
  have hxy : signlessPreprojectiveAFrobeniusFunctional k (x * y) =
      signlessPreprojectiveAFrobeniusFunctional k (e b * x * e a * y) := by
    have hy' : x * y = ∑ b', e b' * (x * e a * y) * e b.rev := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_e, one_mul]
      conv_lhs => rw [← (mem_cornerSubmodule_iff k (isIdempotentElem_e k a)
        (isIdempotentElem_e k b.rev)).mp hy]
      simp only [mul_assoc]
    rw [hy', map_sum, Finset.sum_eq_single b]
    · simp only [mul_assoc]
      rw [mul_eq_self_of_mem_cornerSubmodule_right (isIdempotentElem_e k _) hy]
    · intro b' _ hb'
      exact signlessPreprojectiveAFrobeniusFunctional_mul_mul_eq_zero k
        (by rwa [Fin.rev_rev]) _
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  -- Expand the corner in its valley basis; only the coefficient of the valley with bottom `m`
  -- survives the pairing.
  have hexpand := congrArg Subtype.val
    ((signlessPreprojectiveACornerBasis k a b).sum_repr ⟨_, hz⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    coe_signlessPreprojectiveACornerBasis_apply] at hexpand
  have key := hx y
  rw [hxy, ← hexpand, Finset.sum_mul, map_sum] at key
  simp only [smul_mul_assoc, map_smul, smul_eq_mul, hy_def,
    signlessPreprojectiveAFrobeniusFunctional_valley_mul_valley k a b
      (Subtype.property _) m.property, mul_ite, mul_zero, ← Subtype.ext_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
  exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-! ### Self-injectivity -/

/-- **The signless preprojective algebra of `Aₙ` is left self-injective** over every field. -/
theorem moduleInjective_signlessPreprojectiveAlgebra_A : Module.Injective Π Π :=
  (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).moduleInjective_self

/-- **The signless preprojective algebra of `Aₙ` is right self-injective** over every field. -/
theorem moduleInjective_op_signlessPreprojectiveAlgebra_A : Module.Injective Πᵐᵒᵖ Π :=
  (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).moduleInjective_op_self

/-- **The preprojective algebra of every orientation of `Aₙ` is Frobenius.** The functional is
`TauCeti.signlessPreprojectiveAFrobeniusFunctional`, transported along the sign rescaling which
identifies the signless algebra of the bipartite `Aₙ` graph with the preprojective algebra of the
orientation. -/
theorem exists_isFrobeniusFunctional_preprojectiveAlgebra_A (o : Orientation AG) :
    ∃ φ : preprojectiveAlgebra k (OrientedQuiver AG o) →ₗ[k] k, φ.IsFrobeniusFunctional := by
  have hc : ∀ ⦃i j : OrientedQuiver AG o⦄, (i ⟶ j) →
      diagramGraphAColoring n ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        diagramGraphAColoring n ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => (diagramGraphAColoring n).valid a.1
  exact ⟨_, (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).comp_algEquiv
    ((orientationSignlessPreprojectiveAlgebraEquiv o k).trans
      (symmetrifySignlessPreprojectiveAlgebraEquiv k hc)).symm⟩

/-- **The preprojective algebra of every orientation of `Aₙ` is left self-injective** over every
field. -/
theorem moduleInjective_preprojectiveAlgebra_A (o : Orientation AG) :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver AG o))
      (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  (exists_isFrobeniusFunctional_preprojectiveAlgebra_A k o).choose_spec.moduleInjective_self

/-- **The preprojective algebra of every orientation of `Aₙ` is right self-injective** over every
field. -/
theorem moduleInjective_op_preprojectiveAlgebra_A (o : Orientation AG) :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver AG o))ᵐᵒᵖ
      (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  (exists_isFrobeniusFunctional_preprojectiveAlgebra_A k o).choose_spec.moduleInjective_op_self

end TauCeti
