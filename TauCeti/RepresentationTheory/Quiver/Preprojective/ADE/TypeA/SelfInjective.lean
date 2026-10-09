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
# The preprojective algebra of `Aₙ` is Frobenius and self-injective

Let `Π` be the signless preprojective algebra of the Bourbaki-labelled path
`0 — 1 — ⋯ — (n - 1)`, over a field `k`. Its corner `e_b Π e_a` has the basis of valley classes
`TauCeti.signlessPreprojectiveAValley k a b m` with `a + b + 1 - n ≤ m ≤ min a b`
(`TauCeti.signlessPreprojectiveACornerBasis`): the valley of bottom `m` descends from `a` to `m`
and climbs back to `b`, so it has length `(a - m) + (b - m)`. Write `a' = n - 1 - a`
(`Fin.rev a`). The corner `e_{a'} Π e_a` contains the valley of bottom `0`, of length `n - 1`,
which descends from `a` to `0` and climbs to `a'`.

The functional `TauCeti.signlessPreprojectiveAFrobeniusFunctional` takes `x` to the sum over the
vertices `a` of the coefficient of this bottom-`0` valley in the component `e_{a'} x e_a`. A valley
`v` from `a` to `b` of bottom `m` pairs with the valley from `b` to `a'` of bottom `b - m`: by the
product formula `TauCeti.signlessPreprojectiveAValley_mul`, the product of the latter with a valley
from `a` to `b` of bottom `m'` vanishes for `m' < m` and is, up to sign, the valley from `a` to
`a'` of bottom `m' - m` otherwise. So the functional takes this product to `±1` when `m' = m` and
to `0` otherwise, and the Gram matrix of `(x, y) ↦ φ (x * y)` between the corners `e_{a'} Π e_b` and
`e_b Π e_a` is a signed permutation matrix. Hence `φ` is a Frobenius functional, over every field,
characteristic two included, and `Π` is left and right self-injective. Since `Aₙ` is bipartite,
`Π` is the preprojective algebra of each orientation of `Aₙ` up to a sign rescaling of the arrows,
so these preprojective algebras are self-injective as well.

The vertex `a'` paired with `a` is the image of `a` under the Nakayama permutation
`a ↦ n - 1 - a` of type `A`; socles of the vertex projectives are not computed here.

## Main definitions

* `TauCeti.signlessPreprojectiveAFrobeniusFunctional`: the Frobenius functional.

## Main results

* `TauCeti.signlessPreprojectiveAFrobeniusFunctional_valley`: its value on each basis valley.
* `TauCeti.isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional`: it is a Frobenius
  functional.
* `TauCeti.moduleInjective_signlessPreprojectiveAlgebra_A` and
  `TauCeti.moduleInjective_op_signlessPreprojectiveAlgebra_A`: the signless algebra of `Aₙ` is
  left and right self-injective.
* `TauCeti.moduleInjective_preprojectiveAlgebra_A` and
  `TauCeti.moduleInjective_op_preprojectiveAlgebra_A`: the preprojective algebra of every
  orientation of `Aₙ` is left and right self-injective.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the Frobenius property of the
  preprojective algebras of finite Dynkin type and their Nakayama permutation.
* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra and its local relations.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] finiteNeighborSetFintype

section Field

variable (k : Type*) [Field k] {n : ℕ}

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver AG)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver AG)
local notation "e" => fun a : Fin (DynkinType.A n).rank => π (vertexIdempotent k (vertex AG a))

/-! ### Vertex idempotents and corners -/

/-- The vertex idempotents of `Π`, indexed by the vertices of `Aₙ`, are a complete orthogonal
family. -/
private theorem completeOrthogonalIdempotents_e :
    CompleteOrthogonalIdempotents (e : Fin (DynkinType.A n).rank → Π) := by
  convert (CompleteOrthogonalIdempotents.equiv (vertexEquiv AG)).2
    ((completeOrthogonalIdempotents_vertexIdempotent k (DoubledQuiver AG)).map (π).toRingHom)
    using 1
  ext a
  simp only [Function.comp_apply, vertexEquiv_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- The bottom `0` is an admissible bottom for valleys from `a` to `n - 1 - a`. -/
private theorem zero_mem_Icc_rev (a : Fin (DynkinType.A n).rank) :
    0 ∈ Finset.Icc (a.val + a.rev.val + 1 - n) (min a.val a.rev.val) := by
  have := a.isLt
  have hn := DynkinType.rank_A n
  simp only [Finset.mem_Icc, Fin.val_rev]
  omega

/-! ### The socle coefficients and the Frobenius functional -/

/-- The coefficient of the bottom-`0` valley in the component of an element in the corner from
`a` to `n - 1 - a`. -/
private noncomputable def socleCoeff (a : Fin (DynkinType.A n).rank) : Π →ₗ[k] k :=
  Finsupp.lapply ⟨0, zero_mem_Icc_rev a⟩ ∘ₗ
    (signlessPreprojectiveACornerBasis k a a.rev).repr.toLinearMap ∘ₗ
      (LinearMap.mulLeftRight k (e a.rev, e a)).codRestrict _ fun y => by
        rw [LinearMap.mulLeftRight_apply]
        exact mul_mul_mem_cornerSubmodule k _ _ y

private theorem socleCoeff_apply (a : Fin (DynkinType.A n).rank) (y : Π) :
    socleCoeff k a y = (signlessPreprojectiveACornerBasis k a a.rev).repr
      ⟨e a.rev * y * e a, mul_mul_mem_cornerSubmodule k _ _ y⟩ ⟨0, zero_mem_Icc_rev a⟩ := by
  simp only [socleCoeff, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lapply_apply]
  congr 2
  exact Subtype.ext (by rw [LinearMap.codRestrict_apply, LinearMap.mulLeftRight_apply])

/-- The socle coefficient only depends on the component in its corner. -/
private theorem socleCoeff_congr (a : Fin (DynkinType.A n).rank) {y y' : Π}
    (h : e a.rev * y * e a = e a.rev * y' * e a) : socleCoeff k a y = socleCoeff k a y' := by
  rw [socleCoeff_apply, socleCoeff_apply]
  congr 2
  exact Subtype.ext h

private theorem socleCoeff_eq_zero (a : Fin (DynkinType.A n).rank) {y : Π}
    (h : e a.rev * y * e a = 0) : socleCoeff k a y = 0 := by
  rw [socleCoeff_congr k a (y' := 0) (by rw [h, mul_zero, zero_mul]), map_zero]

/-- On the corner from `a` to `n - 1 - a`, the socle coefficient of a basis valley is `1` for the
valley of bottom `0`, and `0` otherwise. -/
private theorem socleCoeff_valley_rev (a : Fin (DynkinType.A n).rank) {m : ℕ}
    (hm : m ∈ Finset.Icc (a.val + a.rev.val + 1 - n) (min a.val a.rev.val)) :
    socleCoeff k a (signlessPreprojectiveAValley k a a.rev m) = if m = 0 then 1 else 0 := by
  classical
  have he := completeOrthogonalIdempotents_e k (n := n)
  have hv : (⟨e a.rev * signlessPreprojectiveAValley k a a.rev m * e a,
      mul_mul_mem_cornerSubmodule k _ _ _⟩ : cornerSubmodule k (e a.rev) (e a)) =
        signlessPreprojectiveACornerBasis k a a.rev ⟨m, hm⟩ := by
    apply Subtype.ext
    rw [coe_signlessPreprojectiveACornerBasis_apply]
    exact (mem_cornerSubmodule_iff k (he.idem a.rev) (he.idem a)).1
      (signlessPreprojectiveAValley_mem_cornerSubmodule k a a.rev m)
  rw [socleCoeff_apply, hv, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [Subtype.ext_iff, eq_comm (a := m)]

/-- **The Frobenius functional of the signless preprojective algebra of `Aₙ`.** For each vertex
`a`, it reads the coefficient of the valley of bottom `0` from `a` to `n - 1 - a`, a path of
length `n - 1`, in the component of its argument in the corner `e_{n - 1 - a} Π e_a`, and it
adds these coefficients. -/
noncomputable def signlessPreprojectiveAFrobeniusFunctional : Π →ₗ[k] k :=
  ∑ a, socleCoeff k a

/-- **The Frobenius functional on the valley basis.** It takes the value `1` on the valley of
bottom `0` from `a` to `n - 1 - a`, and vanishes on every other basis valley. -/
theorem signlessPreprojectiveAFrobeniusFunctional_valley (a b : Fin (DynkinType.A n).rank) {m : ℕ}
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    signlessPreprojectiveAFrobeniusFunctional k (signlessPreprojectiveAValley k a b m) =
      if b = a.rev ∧ m = 0 then 1 else 0 := by
  classical
  have he := completeOrthogonalIdempotents_e k (n := n)
  have hmem := signlessPreprojectiveAValley_mem_cornerSubmodule k a b m
  rw [signlessPreprojectiveAFrobeniusFunctional, LinearMap.sum_apply, Finset.sum_eq_single a]
  · by_cases hb : b = a.rev
    · subst hb
      rw [socleCoeff_valley_rev k a hm]
      simp only [true_and]
    · rw [ite_eq_right (fun h => hb h.1)]
      apply socleCoeff_eq_zero
      rw [← mul_eq_self_of_mem_cornerSubmodule (he.idem b) hmem]
      simp only [← mul_assoc, he.ortho (Ne.symm hb), zero_mul]
  · intro a' _ ha'
    apply socleCoeff_eq_zero
    rw [← mul_eq_self_of_mem_cornerSubmodule_right (he.idem a) hmem]
    simp only [mul_assoc, he.ortho (Ne.symm ha'), mul_zero]
  · exact fun h => absurd (Finset.mem_univ a) h

/-! ### The Gram matrix -/

/-- Pairing against an element of the corner from `b` to `n - 1 - a` only sees the component of
the second factor in the corner from `a` to `b`. -/
private theorem signlessPreprojectiveAFrobeniusFunctional_mul_eq (a b : Fin (DynkinType.A n).rank)
    {x : Π} (hx : x ∈ cornerSubmodule k (e a.rev) (e b)) (y : Π) :
    signlessPreprojectiveAFrobeniusFunctional k (x * y) =
      signlessPreprojectiveAFrobeniusFunctional k (x * (e b * y * e a)) := by
  have he := completeOrthogonalIdempotents_e k (n := n)
  rw [signlessPreprojectiveAFrobeniusFunctional, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a' _ => socleCoeff_congr k a' ?_
  by_cases ha : a' = a
  · subst ha
    conv_lhs => rw [← mul_eq_self_of_mem_cornerSubmodule_right (he.idem b) hx]
    simp only [mul_assoc, (he.idem a').eq]
  · have hx0 : e a'.rev * x = 0 := by
      rw [← mul_eq_self_of_mem_cornerSubmodule (he.idem a.rev) hx, ← mul_assoc,
        he.ortho (Fin.rev_injective.ne ha), zero_mul]
    simp only [← mul_assoc, hx0, zero_mul]

/-- **The Gram matrix is a signed permutation matrix.** The valley from `b` to `n - 1 - a` of
bottom `b - m` pairs with the valley from `a` to `b` of bottom `m'` to a sign if `m' = m`, and to
`0` otherwise. -/
private theorem signlessPreprojectiveAFrobeniusFunctional_valley_mul_valley
    (a b : Fin (DynkinType.A n).rank) {m m' : ℕ}
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))
    (hm' : m' ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    signlessPreprojectiveAFrobeniusFunctional k
        (signlessPreprojectiveAValley k b a.rev (b.val - m) *
          signlessPreprojectiveAValley k a b m') =
      if m' = m then (-1) ^ (m * (b.val - m)) else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have hn := DynkinType.rank_A n
  have hrev := Fin.val_rev a
  simp only [Finset.mem_Icc] at hm hm'
  rcases lt_or_ge m' m with hlt | hle
  · rw [signlessPreprojectiveAValley_mul_eq_zero k a b a.rev (by omega), map_zero,
      ite_eq_right (by omega)]
  have hbm : b.val - (b.val - m) = m := by omega
  -- The sign is the image of a scalar, so the functional can pull it out.
  have hsign : (-1 : Π) ^ (m * (b.val - m')) = algebraMap k Π ((-1) ^ (m * (b.val - m'))) := by
    rw [map_pow, map_neg, map_one]
  -- The product is, up to sign, the valley from `a` to `n - 1 - a` of bottom `m' - m`.
  rw [signlessPreprojectiveAValley_mul k a b a.rev (by omega) (by omega) (by omega), hbm, hsign,
    ← Algebra.smul_def, map_smul, signlessPreprojectiveAFrobeniusFunctional_valley k a a.rev
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), smul_eq_mul]
  by_cases hmm : m' = m
  · subst hmm
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right (fun h => by omega), ite_eq_right hmm, mul_zero]

/-! ### The Frobenius property -/

/-- **The signless algebra of `Aₙ` is Frobenius**: `(x, y) ↦ φ (x * y)` is nondegenerate on both
sides, over every field. -/
theorem isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional :
    (signlessPreprojectiveAFrobeniusFunctional k (n := n)).IsFrobeniusFunctional := by
  classical
  refine LinearMap.IsFrobeniusFunctional.of_right fun y hy => ?_
  -- Every corner component of `y` vanishes, by pairing it against the dual valleys.
  have hcorner (a b : Fin (DynkinType.A n).rank) : e b * y * e a = 0 := by
    let B := signlessPreprojectiveACornerBasis k a b
    have hz := mul_mul_mem_cornerSubmodule k (e b) (e a) y
    have hsum : e b * y * e a = ∑ i, B.repr ⟨_, hz⟩ i • signlessPreprojectiveAValley k a b i := by
      have h := congrArg Subtype.val (B.sum_repr ⟨_, hz⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, B,
        coe_signlessPreprojectiveACornerBasis_apply] at h
      exact h.symm
    have hrepr : B.repr ⟨_, hz⟩ = 0 := by
      ext ⟨m, hm⟩
      have h := hy (signlessPreprojectiveAValley k b a.rev (b.val - m))
      rw [signlessPreprojectiveAFrobeniusFunctional_mul_eq k a b
        (signlessPreprojectiveAValley_mem_cornerSubmodule k _ _ _), hsum] at h
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
        signlessPreprojectiveAFrobeniusFunctional_valley_mul_valley k a b hm (Subtype.prop _)] at h
      rw [Finset.sum_eq_single ⟨m, hm⟩ (fun i _ hi => by
        rw [ite_eq_right (fun h => hi (Subtype.ext h)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl] at h
      simpa using h
    exact congrArg Subtype.val (B.repr.injective (by rw [hrepr, map_zero]) :
      (⟨_, hz⟩ : cornerSubmodule k (e b) (e a)) = 0)
  -- The corner components of `y` add up to `y`.
  calc y = (∑ b, e b) * y * ∑ a, e a := by
        rw [(completeOrthogonalIdempotents_e k).complete, one_mul, mul_one]
    _ = ∑ a, ∑ b, e b * y * e a := by simp only [Finset.sum_mul, Finset.mul_sum]
    _ = 0 := by simp only [hcorner, Finset.sum_const_zero]

/-- **The signless algebra of `Aₙ` is left self-injective** over every field. -/
theorem moduleInjective_signlessPreprojectiveAlgebra_A : Module.Injective Π Π :=
  (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).moduleInjective_self

/-- **The signless algebra of `Aₙ` is right self-injective** over every field. -/
theorem moduleInjective_op_signlessPreprojectiveAlgebra_A : Module.Injective Πᵐᵒᵖ Π :=
  (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).moduleInjective_op_self

/-! ### Every orientation of `Aₙ` -/

section Orientation

attribute [local instance] RingHomInvPair.of_ringEquiv

variable (o : Orientation (diagramGraph (DynkinType.A n).cartanMatrix))

/-- The signless algebra of the bipartite `Aₙ` graph is the preprojective algebra of each of its
orientations, through the sign rescaling read from the parity colouring of `Aₙ`. -/
private noncomputable def aSignlessEquivPreprojective :
    Π ≃ₐ[k] preprojectiveAlgebra k (OrientedQuiver AG o) :=
  (orientationSignlessPreprojectiveAlgebraEquiv o k).trans
    (symmetrifySignlessPreprojectiveAlgebraEquiv k
      (c := fun i => diagramGraphAColoring n ((OrientedQuiver.vertexEquiv _ o).symm i))
      fun _ _ a => (diagramGraphAColoring n).valid a.1)

/-- **The preprojective algebra of every orientation of `Aₙ` is left self-injective** over every
field. -/
theorem moduleInjective_preprojectiveAlgebra_A :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver AG o))
      (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  have := moduleInjective_signlessPreprojectiveAlgebra_A k (n := n)
  .of_ringEquiv (aSignlessEquivPreprojective k o).toRingEquiv
    (aSignlessEquivPreprojective k o).toRingEquiv.toSemilinearEquiv

/-- **The preprojective algebra of every orientation of `Aₙ` is right self-injective** over every
field. -/
theorem moduleInjective_op_preprojectiveAlgebra_A :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver AG o))ᵐᵒᵖ
      (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  have := moduleInjective_op_signlessPreprojectiveAlgebra_A k (n := n)
  .of_ringEquiv (RingEquiv.op (aSignlessEquivPreprojective k o).toRingEquiv)
    { (aSignlessEquivPreprojective k o).toRingEquiv.toAddEquiv with
      map_smul' := fun r x => by
        rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop]
        exact map_mul (aSignlessEquivPreprojective k o) x r.unop }

end Orientation

end Field

end TauCeti
