/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SurfaceGroup.Basic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Finrank
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.PresentedGroup
public import TauCeti.RepresentationTheory.InvariantForm
import TauCeti.RepresentationTheory.Coinvariants
import TauCeti.RepresentationTheory.Dual

/-!
# One-cocycles and first cohomology of closed surface groups

Let `π = S⁺(g, 0) = ⟨a₁, b₁, …, a_g, b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩` be the fundamental group of the
closed orientable surface of genus `g` (`TauCeti.SurfaceGroup.Orientable g 0`), and let `ρ` be a
representation of `π` on a finite-dimensional vector space `V` over a field `k`. This file
computes the dimensions of the one-cocycles `Z¹(π, V)` and of the first cohomology `H¹(π, V)`:

`dim Z¹(π, V) + dim V = 2g dim V + dim V_π`,
`dim H¹(π, V) + 2 dim V = 2g dim V + dim V^π + dim V_π`,

where `V^π` are the invariants and `V_π = V ⧸ ⟨ρ h v - v⟩` the coinvariants
(`Representation.finrank_cocycles₁_orientable_add_finrank`,
`Representation.finrank_H1_orientable_add_two_mul_finrank`). When `V` carries a nondegenerate
`π`-invariant bilinear form, `V` is self-dual and `dim V_π = dim V^π`, so

`dim Z¹(π, V) = (2g - 1) dim V + dim V^π`,  `dim H¹(π, V) = (2g - 2) dim V + 2 dim V^π`

(`Representation.finrank_cocycles₁_orientable_add_finrank_of_isInvariantForm`,
`Representation.finrank_H1_orientable_add_two_mul_finrank_of_isInvariantForm`). For the adjoint
representation `k_Ad ρ` of a homomorphism `ρ : π → K` into a compact Lie group with an
`Ad`-invariant inner product, `Z¹(π, k_Ad ρ)` is the Zariski tangent space of the representation
variety `Hom(π, K)` at `ρ` and `V^π` is the Lie algebra of the centralizer of `ρ`, so these are
the group-cohomological form of the dimension `(2g - 1) dim k + dim H⁰` of the framed moduli of
flat connections and of the Euler formula `dim H¹ = (2g - 2) dim k + 2 dim H⁰` for their
deformation complex.

## The Fox computation

By `Representation.presentedCocyclesEquiv`, a one-cocycle is its tuple `v` of values at the
`2g` generators, subject to the vanishing of the Fox map of the relator `r`, the value
`c_v(r)` of the free cocycle. So `dim Z¹ = 2g dim V - dim (range of the Fox map)`, and the point is
that the range of the Fox map is exactly the coinvariant kernel `⟨ρ h y - y⟩`
(`Representation.range_foxMap_orientableRelator`).

* The relator is a product of commutators, so its Fox map lands in the coinvariant kernel
  (`Representation.range_foxMap_le_coinvariantsKer`).
* Conversely, let `ψ` be a functional killing the range. Writing `u_i` for the product of the
  first `i` commutators `[a_j, b_j] = a_j⁻¹ b_j⁻¹ a_j b_j`, the free cocycle with value `y` at
  `a_i` and zero at the other generators takes the value
  `ρ u_i ((ρ (a_i⁻¹ b_i⁻¹) - ρ a_i⁻¹) y)` at `r`, and the one with value `y` at `b_i` takes
  `ρ u_i ((ρ (a_i⁻¹ b_i⁻¹ a_i) - ρ (a_i⁻¹ b_i⁻¹)) y)`. By induction on `i`, these two equations
  force `ψ ∘ ρ u_i = ψ` and then `ψ ∘ ρ a_i = ψ ∘ ρ b_i = ψ`, so `ψ` is invariant; by duality the
  range is the whole coinvariant kernel.

## References

* W. M. Goldman, *The symplectic nature of fundamental groups of surfaces*, Advances in
  Mathematics 54 (1984), 200–225, §1 (the Zariski tangent space `Z¹(π; 𝔤_Ad ρ)` and its
  dimension).
* R. H. Fox, *Free differential calculus. I. Derivation in the free group ring*, Annals of
  Mathematics 57 (1953), 547–560.
-/

public section

open CategoryTheory Module groupCohomology TauCeti TauCeti.SurfaceGroup
open scoped commutatorElement

namespace Representation

variable {k : Type} [Field k] {g : ℕ}

/-- The `i`-th commutator `a_i⁻¹ b_i⁻¹ a_i b_i` of the relator of `S⁺(g, 0)`, in the free group. -/
private def handle (i : Fin g) : FreeGroup (OrientableGenerator g 0) :=
  (FreeGroup.of (.a i))⁻¹ * (FreeGroup.of (.b i))⁻¹ * FreeGroup.of (.a i) * FreeGroup.of (.b i)

private theorem orientableRelator_eq_prod : orientableRelator g 0 = (List.ofFn handle).prod := by
  simp only [orientableRelator_def, orientableWord_def, List.ofFn_zero, List.prod_nil, mul_one]
  rfl

section Fox

variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k (Orientable g 0) V)

/-- The Fox map of the surface relator at a tuple supported on the generators of the `i`-th
handle: the value of the free cocycle at the `i`-th commutator, moved by the product of the
earlier commutators. -/
private theorem foxMap_orientableRelator_eq (i : Fin g) (v : OrientableGenerator g 0 → V)
    (hv : ∀ j ≠ i, v (.a j) = 0 ∧ v (.b j) = 0) :
    foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0) v =
      ρ (PresentedGroup.mk _ ((List.ofFn handle).take i).prod)
        (freeCocycle (ρ.comp (PresentedGroup.mk _)) v (handle i)) := by
  set σ := ρ.comp (PresentedGroup.mk {orientableRelator g 0})
  let c := (freeCocycleEquiv σ).symm v
  have hc (w) : c w = freeCocycle σ v w := congrFun (coe_freeCocycleEquiv_symm_apply σ v) w
  have hK (j : Fin g) (hj : j ≠ i) : c (handle j) = 0 := by
    rw [handle, cocycles₁_apply_inv_mul_inv_mul_mul]
    simp [hc, (hv j hj).1, (hv j hj).2]
  have hlen : (List.ofFn (handle (g := g))).length = g := List.length_ofFn
  have hsplit : (List.ofFn handle).prod = ((List.ofFn handle).take i).prod *
      (handle i * ((List.ofFn handle).drop (i + 1)).prod) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn handle)]
    rw [List.prod_append, List.drop_eq_getElem_cons (by omega), List.prod_cons,
      List.getElem_ofFn]
  have htake : c ((List.ofFn handle).take i).prod = 0 :=
    cocycles₁_list_prod_eq_zero c fun x hx ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hx
      rw [List.getElem_ofFn]
      exact hK _ fun h ↦ by simp [Fin.ext_iff] at h; omega
  have hdrop : c ((List.ofFn handle).drop (i + 1)).prod = 0 :=
    cocycles₁_list_prod_eq_zero c fun x hx ↦ by
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.1 hx
      rw [List.getElem_ofFn]
      exact hK _ fun h ↦ by simp [Fin.ext_iff] at h; omega
  rw [foxMap_apply, ← hc, congrArg (⇑c) orientableRelator_eq_prod, hsplit, cocycles₁_map_mul,
    cocycles₁_map_mul, hdrop, htake, map_zero, zero_add, add_zero, hc, Rep.of_ρ,
    MonoidHom.comp_apply]

/-- The value at the `i`-th commutator of the free cocycle with value `y` at `a_i` and zero at
the other generators. -/
private theorem freeCocycle_single_a_handle (i : Fin g) (y : V) :
    freeCocycle (ρ.comp (PresentedGroup.mk _)) (Pi.single (.a i) y) (handle i) =
      ρ (Orientable.a g 0 i)⁻¹ (ρ (Orientable.b g 0 i)⁻¹ y) - ρ (Orientable.a g 0 i)⁻¹ y := by
  have := cocycles₁_apply_inv_mul_inv_mul_mul
    ((freeCocycleEquiv (ρ.comp (PresentedGroup.mk {orientableRelator g 0}))).symm
      (Pi.single (.a i) y)) (FreeGroup.of (.a i)) (FreeGroup.of (.b i))
  simp only [coe_freeCocycleEquiv_symm_apply, freeCocycle_of, Pi.single_eq_same,
    ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, map_zero, sub_zero,
    add_zero] at this
  rw [handle, this]
  simp [Orientable.a_def, Orientable.b_def, PresentedGroup.of, mul_apply_eq_comp]

/-- The value at the `i`-th commutator of the free cocycle with value `y` at `b_i` and zero at
the other generators. -/
private theorem freeCocycle_single_b_handle (i : Fin g) (y : V) :
    freeCocycle (ρ.comp (PresentedGroup.mk _)) (Pi.single (.b i) y) (handle i) =
      ρ (Orientable.a g 0 i)⁻¹ (ρ (Orientable.b g 0 i)⁻¹ (ρ (Orientable.a g 0 i) y)) -
        ρ (Orientable.a g 0 i)⁻¹ (ρ (Orientable.b g 0 i)⁻¹ y) := by
  have := cocycles₁_apply_inv_mul_inv_mul_mul
    ((freeCocycleEquiv (ρ.comp (PresentedGroup.mk {orientableRelator g 0}))).symm
      (Pi.single (.b i) y)) (FreeGroup.of (.a i)) (FreeGroup.of (.b i))
  simp only [coe_freeCocycleEquiv_symm_apply, freeCocycle_of, Pi.single_eq_same,
    ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, map_zero, sub_zero,
    zero_add] at this
  rw [handle, this]
  simp [Orientable.a_def, Orientable.b_def, PresentedGroup.of, mul_apply_eq_comp]

/-- A functional invariant under `c` is invariant under `c⁻¹`. -/
private theorem apply_inv_eq {ψ : Module.Dual k V} {c : Orientable g 0}
    (hc : ∀ y, ψ (ρ c y) = ψ y) (y : V) : ψ (ρ c⁻¹ y) = ψ y := by
  rw [← hc, self_inv_apply]

/-- The two equations which the Fox map of one handle imposes on a functional `ψ` force `ψ` to be
invariant under both generators `a` and `b` of the handle. -/
private theorem apply_eq_of_handle {ψ : Module.Dual k V} {a b : Orientable g 0}
    (h₁ : ∀ y, ψ (ρ a⁻¹ (ρ b⁻¹ y)) = ψ (ρ a⁻¹ y))
    (h₂ : ∀ y, ψ (ρ a⁻¹ (ρ b⁻¹ (ρ a y))) = ψ (ρ a⁻¹ (ρ b⁻¹ y))) :
    (∀ y, ψ (ρ a y) = ψ y) ∧ ∀ y, ψ (ρ b y) = ψ y := by
  have ha' (y : V) : ψ (ρ a⁻¹ y) = ψ y := by
    rw [← h₁, ← h₂, h₁, inv_self_apply]
  have hb' (y : V) : ψ (ρ b⁻¹ y) = ψ y := by
    rw [← ha' (ρ b⁻¹ y), h₁, ha']
  exact ⟨fun y ↦ by rw [← ha' (ρ a y), inv_self_apply],
    fun y ↦ by rw [← hb' (ρ b y), inv_self_apply]⟩

/-- Induction along the handles: a functional killing the range of the Fox map of the surface
relator is invariant under the product `u_n` of the first `n` commutators and under the
generators of the first `n` handles. -/
private theorem apply_eq_of_forall_foxMap_take (ψ : Module.Dual k V)
    (hψ : ∀ v, ψ (foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0) v) = 0) (n : ℕ)
    (hn : n ≤ g) :
    (∀ y, ψ (ρ (PresentedGroup.mk _ ((List.ofFn handle).take n).prod) y) = ψ y) ∧
      ∀ j : Fin g, (j : ℕ) < n →
        (∀ y, ψ (ρ (Orientable.a g 0 j) y) = ψ y) ∧ ∀ y, ψ (ρ (Orientable.b g 0 j) y) = ψ y := by
  induction n with
  | zero => exact ⟨fun y ↦ by simp, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨hP, hgen⟩ := ih (by omega)
    set i : Fin g := ⟨n, by omega⟩
    have hsupp (x : OrientableGenerator g 0) (y : V) (hx : x = .a i ∨ x = .b i) :
        ∀ j ≠ i, (Pi.single x y : OrientableGenerator g 0 → V) (.a j) = 0 ∧
          (Pi.single x y : OrientableGenerator g 0 → V) (.b j) = 0 := by
      intro j hj
      rcases hx with rfl | rfl <;> simp [hj]
    -- The two equations imposed by the generators of the `n`-th handle.
    obtain ⟨ha, hb⟩ := apply_eq_of_handle ρ (ψ := ψ) (a := Orientable.a g 0 i)
      (b := Orientable.b g 0 i) (fun y ↦ by
        have := hψ (Pi.single (.a i) y)
        rwa [foxMap_orientableRelator_eq ρ i _ (hsupp _ y (.inl rfl)), hP,
          freeCocycle_single_a_handle, map_sub, sub_eq_zero] at this) (fun y ↦ by
        have := hψ (Pi.single (.b i) y)
        rwa [foxMap_orientableRelator_eq ρ i _ (hsupp _ y (.inr rfl)), hP,
          freeCocycle_single_b_handle, map_sub, sub_eq_zero] at this)
    refine ⟨fun y ↦ ?_, fun j hj ↦ ?_⟩
    · have hmk : PresentedGroup.mk {orientableRelator g 0} (handle i) =
          (Orientable.a g 0 i)⁻¹ * (Orientable.b g 0 i)⁻¹ * Orientable.a g 0 i *
            Orientable.b g 0 i := by
        simp [handle, Orientable.a_def, Orientable.b_def, PresentedGroup.of]
      rw [List.prod_take_succ _ _ (by simp; omega), List.getElem_ofFn, map_mul, map_mul,
        mul_apply_eq_comp, hP, hmk]
      simp only [map_mul, mul_apply_eq_comp, hb, ha, apply_inv_eq ρ hb, apply_inv_eq ρ ha]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hgen j hj
      · obtain rfl : j = i := Fin.ext hj
        exact ⟨ha, hb⟩

/-- **A functional killing the range of the Fox map of the surface relator is invariant.** -/
private theorem apply_eq_of_forall_foxMap_orientableRelator (ψ : Module.Dual k V)
    (hψ : ∀ v, ψ (foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0) v) = 0)
    (h : Orientable g 0) (y : V) :
    ψ (ρ h y) = ψ y := by
  have hgen := (apply_eq_of_forall_foxMap_take ρ ψ hψ g le_rfl).2
  induction (PresentedGroup.closure_range_of _).ge (Subgroup.mem_top h)
    using Subgroup.closure_induction generalizing y with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    rcases x with j | j | j
    · exact Orientable.a_def g 0 j ▸ (hgen j j.isLt).1 y
    · exact Orientable.b_def g 0 j ▸ (hgen j j.isLt).2 y
    · exact j.elim0
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, mul_apply_eq_comp, ha, hb]
  | inv a _ ha => exact apply_inv_eq ρ ha y

/-- **The range of the Fox map of the surface relator is the coinvariant kernel.** The Fox map
`v ↦ c_v(r)` of the relator `r = [a₁, b₁] ⋯ [a_g, b_g]` of `S⁺(g, 0)` has range the span of the
`ρ h y - y`. -/
theorem range_foxMap_orientableRelator :
    LinearMap.range (foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0)) =
      Coinvariants.ker ρ := by
  refine le_antisymm ?_ ?_
  · rw [← coinvariantsKer_comp_of_surjective _ _ (PresentedGroup.mk_surjective _)]
    exact range_foxMap_le_coinvariantsKer _ (orientableRelator_mem_commutator g)
  · rw [← Subspace.dualAnnihilator_le_dualAnnihilator_iff, dualAnnihilator_coinvariantsKer]
    intro ψ hψ
    rw [Submodule.mem_dualAnnihilator] at hψ
    exact TauCeti.Representation.mem_invariants_dual_iff.2 fun h y ↦
      apply_eq_of_forall_foxMap_orientableRelator ρ ψ (fun v ↦ hψ _ ⟨v, rfl⟩) h y

variable [FiniteDimensional k V]

private theorem card_orientableGenerator : Fintype.card (OrientableGenerator g 0) = 2 * g := by
  rw [Fintype.card_congr (OrientableGenerator.equivSum g 0)]
  simp [two_mul]

/-- **The dimension of the one-cocycles of a closed surface group.** For a representation of
`S⁺(g, 0)` on a finite-dimensional space `V`,
`dim Z¹(S⁺(g, 0), V) + dim V = 2g dim V + dim V_π`, where `V_π` is the space of coinvariants. -/
theorem finrank_cocycles₁_orientable_add_finrank :
    finrank k (cocycles₁ (Rep.of ρ)) + finrank k V =
      2 * g * finrank k V + finrank k ρ.Coinvariants := by
  have hZ : finrank k (cocycles₁ (Rep.of ρ)) = finrank k
      (LinearMap.ker (foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0))) := by
    rw [(presentedCocyclesEquiv ρ).finrank_eq, iInf_singleton]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (foxMap (ρ.comp (PresentedGroup.mk _)) (orientableRelator g 0))
  -- `ρ.Coinvariants` is by definition the quotient `V ⧸ Coinvariants.ker ρ`.
  have hq : finrank k ρ.Coinvariants + finrank k (Coinvariants.ker ρ) = finrank k V :=
    Submodule.finrank_quotient_add_finrank (Coinvariants.ker ρ)
  rw [range_foxMap_orientableRelator, Module.finrank_pi_fintype] at hrn
  simp only [Finset.sum_const, Finset.card_univ, card_orientableGenerator, smul_eq_mul] at hrn
  omega

end Fox

section Cohomology

variable {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k (Orientable g 0) V)

/-- **The dimension of the first cohomology of a closed surface group.** For a representation of
`S⁺(g, 0)` on a finite-dimensional space `V`,
`dim H¹(S⁺(g, 0), V) + 2 dim V = 2g dim V + dim V^π + dim V_π`, where `V^π` and `V_π` are the
invariants and the coinvariants. -/
theorem finrank_H1_orientable_add_two_mul_finrank :
    finrank k (H1 (Rep.of ρ)) + 2 * finrank k V =
      2 * g * finrank k V + finrank k ρ.invariants + finrank k ρ.Coinvariants := by
  have h₁ := finrank_cocycles₁_orientable_add_finrank ρ
  -- `Rep.of ρ` has carrier `V` and representation `ρ` by definition.
  have h₂ : finrank k (coboundaries₁ (Rep.of ρ)) + finrank k ρ.invariants = finrank k V :=
    finrank_coboundaries₁_add_finrank_invariants (Rep.of ρ)
  have h₃ := finrank_H1_add_finrank_coboundaries₁ (Rep.of ρ)
  omega

variable {B : LinearMap.BilinForm k V}

/-- **The dimension of the one-cocycles of a closed surface group, for a self-dual
representation.** If `V` carries a nondegenerate `π`-invariant bilinear form, then
`dim Z¹(S⁺(g, 0), V) + dim V = 2g dim V + dim V^π`, that is
`dim Z¹ = (2g - 1) dim V + dim V^π`. -/
theorem finrank_cocycles₁_orientable_add_finrank_of_isInvariantForm
    (hB : TauCeti.Representation.IsInvariantForm ρ B) (hB' : B.Nondegenerate) :
    finrank k (cocycles₁ (Rep.of ρ)) + finrank k V =
      2 * g * finrank k V + finrank k ρ.invariants := by
  rw [finrank_cocycles₁_orientable_add_finrank,
    finrank_coinvariants_eq_finrank_invariants_dual,
    (hB.equivDual hB').invariantsLinearEquiv.finrank_eq]

/-- **The Euler formula for the first cohomology of a closed surface group.** If `V` carries a
nondegenerate `π`-invariant bilinear form, then
`dim H¹(S⁺(g, 0), V) + 2 dim V = 2g dim V + 2 dim V^π`, that is
`dim H¹ = (2g - 2) dim V + 2 dim V^π`. -/
theorem finrank_H1_orientable_add_two_mul_finrank_of_isInvariantForm
    (hB : TauCeti.Representation.IsInvariantForm ρ B) (hB' : B.Nondegenerate) :
    finrank k (H1 (Rep.of ρ)) + 2 * finrank k V =
      2 * g * finrank k V + 2 * finrank k ρ.invariants := by
  rw [finrank_H1_orientable_add_two_mul_finrank,
    finrank_coinvariants_eq_finrank_invariants_dual,
    (hB.equivDual hB').invariantsLinearEquiv.finrank_eq]
  ring

end Cohomology

end Representation
