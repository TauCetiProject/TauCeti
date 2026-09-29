/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Prescription
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.MinimalPresentation

/-!
# The prescription property of a presented pro-`p` group

Let `G = ⟨X ∣ rels⟩` be the pro-`p` group presented on a finite type `X` by a set of relators
`rels` in the free pro-`p` group `F = freeProP p X`, and let `χ : G →ₜ* ℤ_pˣ` be a continuous
character. Labute's prescription property of `χ` (`TauCeti.HasPrescriptionProperty`) says that
every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective; for a topologically finitely
generated pro-`p` group it says that continuous crossed homomorphisms `G → ℤ_p` for `χ` take any
prescribed values on a minimal generating tuple.

For a presented group this becomes a condition on the relators alone. A continuous crossed
homomorphism `F → ℤ_p` for the character `χ ∘ mk` of the free group is determined by its values on
the generators and takes any prescribed values there, and it descends to `G` exactly when it kills
the relators. Hence **`χ` has the prescription property if and only if every continuous crossed
homomorphism `F → ℤ_p` for `χ ∘ mk` vanishes on every relator**
(`TauCeti.presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero`), when the
presentation is minimal, that is when the relators lie in the Frattini subgroup of `F`; the
sufficiency of the condition needs no minimality. For a one-relator group this is the vanishing of
a single `ℤ_p`-linear form in the values on the generators, whose coefficients are polynomial in
the values of `χ`; computing it on the normal-form relators of the Demushkin groups is how the
canonical character of each normal form is found (Labute, Theorem 4).

## Main results

* `TauCeti.presentedProP.exists_continuous_isCrossedHom_comp_mk_eq`: a continuous crossed
  homomorphism of the free group for `χ ∘ mk` that kills the relators descends to a continuous
  crossed homomorphism of the presented group for `χ`.
* `TauCeti.presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero`: if every
  continuous crossed homomorphism of the free group for `χ ∘ mk` kills the relators, then `χ` has
  the prescription property.
* `TauCeti.presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero`: for a minimal
  presentation, the converse holds as well.
* `TauCeti.HasPrescriptionProperty.exists_continuous_isCrossedHom_comp_mk_forall_apply_of_eq`: for
  a minimal presentation, a character with the prescription property admits a continuous crossed
  homomorphism of the free group for `χ ∘ mk` with any prescribed values on the generators that
  kills the relators; `…_forall_freeProPGen_eq_ite` is the Kronecker case on a presentation on
  `Fin n`, the form in which the relator computations read off one coefficient at a time.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6 and Theorem 4.
-/

public section

namespace TauCeti

universe u

open Topology

variable {p : ℕ} [Fact p.Prime] {X : Type u} {rels : Set (freeProP p X)}

namespace presentedProP

variable {χ : presentedProP p X rels →ₜ* ℤ_[p]ˣ}

/-- **Descent of crossed homomorphisms along a presentation.** A continuous crossed homomorphism
`F : freeProP p X → ℤ_p` for the character `χ ∘ mk` that vanishes on every relator is constant on
the cosets of the relation subgroup, so it is `F' ∘ mk` for a continuous crossed homomorphism
`F' : ⟨X ∣ rels⟩ → ℤ_p` for `χ`. -/
theorem exists_continuous_isCrossedHom_comp_mk_eq {F : freeProP p X → ℤ_[p]} (hFc : Continuous F)
    (hF : IsCrossedHom (χ.comp (mk p rels)) F) (h : ∀ r ∈ rels, F r = 0) :
    ∃ F' : presentedProP p X rels → ℤ_[p],
      Continuous F' ∧ IsCrossedHom χ F' ∧ F' ∘ mk p rels = F := by
  have hχ : ∀ x, mk p rels x = 1 → ((χ.comp (mk p rels)) x : ℤ_[p]) = 1 := fun x hx ↦ by
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hx, map_one, Units.val_one]
  -- The elements of the kernel of `mk` killed by `F` form a closed normal subgroup containing the
  -- relators, hence containing the relation subgroup.
  let K : Subgroup (freeProP p X) :=
    { carrier := {x | mk p rels x = 1 ∧ F x = 0}
      one_mem' := ⟨map_one _, hF.map_one⟩
      mul_mem' := fun {x y} hx hy ↦
        ⟨by rw [map_mul, hx.1, hy.1, one_mul], by rw [hF.map_mul, hx.2, hy.2, mul_zero, zero_add]⟩
      inv_mem' := fun {x} hx ↦
        ⟨by rw [map_inv, hx.1, inv_one], by rw [hF.map_inv, hx.2, mul_zero]⟩ }
  have : K.Normal := ⟨fun x hx g ↦
    ⟨by rw [map_mul, map_mul, hx.1, mul_one, map_inv, mul_inv_cancel], by
      have h1 := hF.map_mul g (x * g⁻¹)
      rw [hF.map_mul x g⁻¹, hx.2, hχ x hx.1, one_mul, add_zero, ← hF.map_mul g g⁻¹,
        mul_inv_cancel, hF.map_one] at h1
      rwa [mul_assoc]⟩⟩
  have hKclosed : IsClosed (K : Set (freeProP p X)) :=
    (isClosed_eq (map_continuous (mk p rels)) continuous_const).inter
      (isClosed_eq hFc continuous_const)
  have hle : (Subgroup.normalClosure rels).topologicalClosure ≤ K :=
    Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal fun r hr ↦ ⟨mk_relator r hr, h r hr⟩) hKclosed
  -- `F` is constant on the cosets of the relation subgroup.
  have hconst : ∀ x y, mk p rels x = mk p rels y → F x = F y := fun x y hxy ↦ by
    have hmem : x⁻¹ * y ∈ (Subgroup.normalClosure rels).topologicalClosure := by
      rw [← mk_eq_one_iff, map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := hF.map_mul x (x⁻¹ * y)
    rw [mul_inv_cancel_left, (hle hmem).2, mul_zero, zero_add] at h1
    exact h1.symm
  obtain ⟨F', hF'⟩ : ∃ F' : presentedProP p X rels → ℤ_[p], ∀ x, F' (mk p rels x) = F x :=
    ⟨F ∘ Function.surjInv (mk_surjective p rels),
      fun x ↦ hconst _ _ (Function.surjInv_eq (mk_surjective p rels) (mk p rels x))⟩
  have hcomp : F' ∘ mk p rels = F := funext hF'
  refine ⟨F', ?_, isCrossedHom_iff.2 fun a b ↦ ?_, hcomp⟩
  · -- `mk` is a continuous surjection from a compact space onto a Hausdorff space, hence a quotient
    -- map, and `F' ∘ mk = F` is continuous.
    have hq : IsQuotientMap (mk p rels) :=
      (map_continuous (mk p rels)).isClosedMap.isQuotientMap (map_continuous _)
        (mk_surjective p rels)
    rw [hq.continuous_iff, hcomp]
    exact hFc
  · obtain ⟨x, rfl⟩ := mk_surjective p rels a
    obtain ⟨y, rfl⟩ := mk_surjective p rels b
    rw [← map_mul, hF', hF', hF', hF.map_mul, ContinuousMonoidHom.coe_comp, Function.comp_apply]

variable [Finite X]

/-- **Crossed homomorphisms killing the relators give the prescription property.** If every
continuous crossed homomorphism `freeProP p X → ℤ_p` for `χ ∘ mk` vanishes on every relator, then
`χ` has the prescription property: any values on the generators are attained by a continuous crossed
homomorphism of the free group, which descends to the presented group. No minimality of the
presentation is needed. -/
theorem hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
    (h : ∀ F : freeProP p X → ℤ_[p], Continuous F → IsCrossedHom (χ.comp (mk p rels)) F →
      ∀ r ∈ rels, F r = 0) :
    HasPrescriptionProperty χ := by
  refine hasPrescriptionProperty_of_forall_exists_continuous_forall_mul_eq_and_apply_eq
    topologicalClosure_closure_range_of_eq_top fun c ↦ ?_
  obtain ⟨F, hFc, hF, hFv⟩ :=
    freeProP.exists_continuous_isCrossedHom_forall_apply_of_eq (χ.comp (mk p rels)) c
  obtain ⟨F', hF'c, hF', hF'F⟩ := exists_continuous_isCrossedHom_comp_mk_eq hFc hF (h F hFc hF)
  exact ⟨F', hF'c, hF'.map_mul, fun x ↦ by rw [← mk_of, ← hFv x, ← hF'F, Function.comp_apply]⟩

/-- **The prescription property of a minimally presented pro-`p` group is a condition on the
relators** (Labute, Proposition 6, read on a presentation). For a presentation whose relators lie in
the Frattini subgroup of the free pro-`p` group, a continuous character `χ` has the prescription
property exactly when every continuous crossed homomorphism `freeProP p X → ℤ_p` for `χ ∘ mk`
vanishes on every relator. -/
theorem hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (χ : presentedProP p X rels →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔
      ∀ F : freeProP p X → ℤ_[p], Continuous F → IsCrossedHom (χ.comp (mk p rels)) F →
        ∀ r ∈ rels, F r = 0 := by
  refine ⟨fun hχ F hFc hF r hr ↦ ?_, hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero⟩
  -- The values of `F` on the generators are attained by a crossed homomorphism of the presented
  -- group; its composite with `mk` agrees with `F` on the generators, hence everywhere.
  obtain ⟨F', hF'c, hF'mul, hF'v⟩ := hχ.exists_continuous_forall_mul_eq_and_apply_eq
    (isProP p X rels) isTopologicallyFinitelyGenerated
    (linearIndependent_frattiniQuotient_of rels hrels) fun x ↦ F (freeProP.of x)
  have hF' : IsCrossedHom χ F' := isCrossedHom_iff.2 hF'mul
  have heq : F' ∘ mk p rels = F :=
    (hF'.comp (mk p rels) fun x ↦ congrFun (ContinuousMonoidHom.coe_comp χ (mk p rels)) x)
      |>.eq_of_eqOn_of_topologicalClosure_closure_eq_top hF (hF'c.comp (map_continuous _)) hFc
        (freeProP.topologicalClosure_closure_range_of_eq_top p X)
        (by rintro _ ⟨x, rfl⟩; simpa using hF'v x)
  rw [← heq, Function.comp_apply, mk_relator r hr, hF'.map_one]

end presentedProP

namespace HasPrescriptionProperty

variable [Finite X] {χ : presentedProP p X rels →ₜ* ℤ_[p]ˣ}

/-- **Prescribed values on the generators, killing the relators.** For a minimal presentation, a
character `χ` with the prescription property admits, for every `c : X → ℤ_p`, a continuous crossed
homomorphism of the free group for `χ ∘ mk` taking the value `c x` at the generator `x` and
vanishing on every relator. -/
theorem exists_continuous_isCrossedHom_comp_mk_forall_apply_of_eq (hχ : HasPrescriptionProperty χ)
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (c : X → ℤ_[p]) :
    ∃ F : freeProP p X → ℤ_[p], Continuous F ∧ IsCrossedHom (χ.comp (presentedProP.mk p rels)) F ∧
      (∀ x, F (freeProP.of x) = c x) ∧ ∀ r ∈ rels, F r = 0 := by
  rw [presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero hrels] at hχ
  obtain ⟨F, hFc, hF, hFv⟩ := freeProP.exists_continuous_isCrossedHom_forall_apply_of_eq
    (χ.comp (presentedProP.mk p rels)) c
  exact ⟨F, hFc, hF, hFv, hχ F hFc hF⟩

/-- **The Kronecker crossed homomorphism of a minimal presentation on `Fin n`.** For `j < n`, a
character `χ` with the prescription property admits a crossed homomorphism of the free group for
`χ ∘ mk` taking the value `1` at the `j`-th `ℕ`-indexed generator and `0` at every other one, and
vanishing on every relator. -/
theorem exists_isCrossedHom_comp_mk_forall_freeProPGen_eq_ite {n : ℕ}
    {rels : Set (freeProP p (Fin n))} {χ : presentedProP p (Fin n) rels →ₜ* ℤ_[p]ˣ}
    (hχ : HasPrescriptionProperty χ) (hrels : rels ⊆ proPFrattini p (freeProP p (Fin n))) {j : ℕ}
    (hj : j < n) :
    ∃ F : freeProP p (Fin n) → ℤ_[p], IsCrossedHom (χ.comp (presentedProP.mk p rels)) F ∧
      (∀ i, F (freeProPGen p n i) = if i = j then 1 else 0) ∧ ∀ r ∈ rels, F r = 0 := by
  obtain ⟨F, -, hF, hFv, hFr⟩ := hχ.exists_continuous_isCrossedHom_comp_mk_forall_apply_of_eq
    hrels fun i : Fin n ↦ if (i : ℕ) = j then (1 : ℤ_[p]) else 0
  refine ⟨F, hF, fun i ↦ ?_, hFr⟩
  by_cases hi : i < n
  · rw [freeProPGen_of_lt p hi, hFv]
  · rw [freeProPGen_eq_one_of_le p (not_lt.1 hi), hF.map_one, ite_eq_right (by omega)]

end HasPrescriptionProperty

end TauCeti
