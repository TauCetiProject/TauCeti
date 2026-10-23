/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Equationally Noetherian groups

A group `H` receiving the coefficients `G` through `ι : G →* H` is *equationally Noetherian* when
every system of equations `S ⊆ G[X]` in finitely many variables is equivalent over `H` to a finite
subsystem: some finite `S₀ ⊆ S` has the same solutions `V_H(S₀) = V_H(S)`, and then the same
radical. Baumslag, Myasnikov and Remeslennikov show that this is equivalent to the descending
chain condition on the algebraic sets over `H`, which is what makes them finite unions of
irreducible components. The definition asserts only the existence of `S₀`, not a way of finding
it.

The property passes to subgroups (more precisely, to the source of an injective homomorphism
compatible with the coefficients) and survives restriction of the coefficients along any
homomorphism `G' →* G`. Finite groups are equationally Noetherian, and so are finitely generated
commutative groups such as `ℤ`, because a system over a commutative group is a system of linear
equations whose coefficient vectors span a finitely generated `ℤ`-module. The property is not
automatic: in a direct product of infinitely many copies of a nonabelian group, the system
`[x, aᵢ] = 1` asking `x` to commute with the copy `aᵢ` of a fixed element in every coordinate is
equivalent to none of its finite subsystems.

## Main definitions

* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian ι`: every system in finitely many variables has
  a finite subsystem with the same solutions in `H`.

## Main results

* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.exists_finite`,
  `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.exists_finite_Rad_eq`: the finite subsystem, for
  any finite type of variables, with the same algebraic set and the same radical.
* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.of_injective`: subgroups of equationally
  Noetherian groups are equationally Noetherian.
* `TauCeti.GroupAlgGeom.IsEquationallyNoetherian.comp`: restricting the coefficients preserves the
  property.
* `TauCeti.GroupAlgGeom.isEquationallyNoetherian_of_finite`,
  `TauCeti.GroupAlgGeom.isEquationallyNoetherian_of_commGroup_of_fg`: finite groups and finitely
  generated commutative groups are equationally Noetherian.
* `TauCeti.GroupAlgGeom.exists_subsingleton_V_eq`: with at most one point, for instance with no
  variables, a single equation suffices.
* `TauCeti.GroupAlgGeom.not_isEquationallyNoetherian_pi`: an infinite direct power of a nonabelian
  group is not equationally Noetherian over itself.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1 and §2.2 (Theorem 1 and Proposition 4).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod
open scoped commutatorElement

variable {G G' H K X Y : Type*} [Group G] [Group G'] [Group H] [Group K]

/-- `H` is equationally Noetherian over the coefficients `ι : G →* H` when every system of
equations `S ⊆ G[X]` in finitely many variables has a finite subsystem `S₀ ⊆ S` with the same
solutions in `H`. The variables are taken to be `Fin n`; see
`IsEquationallyNoetherian.exists_finite` for an arbitrary finite type of variables. -/
def IsEquationallyNoetherian (ι : G →* H) : Prop :=
  ∀ (n : ℕ) (S : Set (GX G (Fin n))), ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S

/-- A homomorphism `m : G[X] →* G'[Y]` together with a map of points `θ` compatible with
evaluation carries finite subsystems of `m(S)` with the same solutions back to finite subsystems
of `S` with the same solutions. -/
private theorem exists_finite_V_eq_of_map {ι : G →* H} {ι' : G' →* H}
    (m : GX G X →* GX G' Y) (θ : (X → H) → (Y → H))
    (hθ : ∀ v s, eval ι' (θ v) (m s) = eval ι v s) {S : Set (GX G X)}
    (h : ∃ T ⊆ m '' S, T.Finite ∧ V ι' T = V ι' (m '' S)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  obtain ⟨S₀, hS₀, hfin, hV⟩ := Set.exists_subset_image_finite_and.1 h
  have key (T : Set (GX G X)) : V ι T = θ ⁻¹' V ι' (m '' T) := by
    ext v
    simp [hθ]
  exact ⟨S₀, hS₀, hfin, by rw [key, key, hV]⟩

namespace IsEquationallyNoetherian

variable {ι : G →* H}

/-- Over an equationally Noetherian group, every system in a finite type of variables has a
finite subsystem with the same solutions. -/
theorem exists_finite (h : IsEquationallyNoetherian ι) [Finite X] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  exact exists_finite_V_eq_of_map (Monoid.Coprod.map (.id G) (FreeGroup.map e)) (· ∘ e.symm)
    (fun v s => by simp [Function.comp_assoc]) (h n _)

/-- Over an equationally Noetherian group, every system in a finite type of variables has a
finite subsystem with the same radical. -/
theorem exists_finite_Rad_eq (h : IsEquationallyNoetherian ι) [Finite X] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ Rad ι S₀ = Rad ι S := by
  obtain ⟨S₀, hS₀, hfin, hV⟩ := h.exists_finite S
  exact ⟨S₀, hS₀, hfin, by rw [Rad_def, Rad_def, hV]⟩

/-- The source of an injective homomorphism compatible with the coefficients into an equationally
Noetherian group is equationally Noetherian; in particular so is every subgroup containing the
image of the coefficients. -/
theorem of_injective {ιK : G →* K} (h : IsEquationallyNoetherian ι) (f : GHom ιK ι)
    (hf : Function.Injective f) : IsEquationallyNoetherian ιK := by
  intro n S
  obtain ⟨S₀, hS₀, hfin, hV⟩ := h n S
  have key (T : Set (GX G (Fin n))) : V ιK T = (f ∘ ·) ⁻¹' V ι T := by
    ext v
    simp only [mem_V, Set.mem_preimage, ← map_eval f, map_eq_one_iff f hf]
  exact ⟨S₀, hS₀, hfin, by rw [key, key, hV]⟩

/-- Restricting the coefficients along a homomorphism `f : G' →* G` preserves equational
Noetherianity. In particular a group which is equationally Noetherian over itself is equationally
Noetherian over each of its subgroups. -/
theorem comp (h : IsEquationallyNoetherian ι) (f : G' →* G) :
    IsEquationallyNoetherian (ι.comp f) := fun n _ =>
  exists_finite_V_eq_of_map (Monoid.Coprod.map f (FreeGroup.map id)) id
    (fun v s => by simp) (h n _)

end IsEquationallyNoetherian

/-- The equational Noetherianity of `H` does not depend on how the variables are indexed: it
holds if and only if every system in any finite type of variables, in any universe, has a finite
subsystem with the same solutions. -/
theorem isEquationallyNoetherian_iff {ι : G →* H} :
    IsEquationallyNoetherian ι ↔
      ∀ (X : Type*) [Finite X] (S : Set (GX G X)), ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S :=
  ⟨fun h _ _ S => h.exists_finite S, fun h n _ =>
    exists_finite_V_eq_of_map (Monoid.Coprod.map (.id G) (FreeGroup.map ULift.up))
      (· ∘ ULift.down) (fun _ _ => by simp [Function.comp_def]) (h (ULift (Fin n)) _)⟩

/-! ### Finite groups and systems with few points -/

/-- If there are only finitely many points `X → H`, every system is equivalent to a finite
subsystem: one equation failing at each non-solution suffices. -/
theorem exists_finite_V_eq_of_finite {ι : G →* H} [Finite (X → H)] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  have hw (v : ↥(V ι S)ᶜ) : ∃ s ∈ S, eval ι v s ≠ 1 := by
    have hv := v.2
    simpa only [Set.mem_compl_iff, mem_V, not_forall, exists_prop] using hv
  choose w hwS hw using hw
  have hsub : Set.range w ⊆ S := Set.range_subset_iff.2 hwS
  refine ⟨Set.range w, hsub, Set.finite_range w, (V_antitone ι hsub).antisymm' fun v hv => ?_⟩
  by_contra hvS
  exact hw ⟨v, hvS⟩ (mem_V.1 hv _ ⟨⟨v, hvS⟩, rfl⟩)

/-- Finite groups are equationally Noetherian, over any coefficients. -/
theorem isEquationallyNoetherian_of_finite [Finite H] (ι : G →* H) :
    IsEquationallyNoetherian ι := fun _ S =>
  exists_finite_V_eq_of_finite S

/-- If there is at most one point `X → H`, for instance when there are no variables, a single
equation suffices: a system with a solution is equivalent to the empty subsystem, and a system
without one is equivalent to any of its equations that fails at the point. -/
theorem exists_subsingleton_V_eq {ι : G →* H} [Subsingleton (X → H)] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Subsingleton ∧ V ι S₀ = V ι S := by
  by_cases hS : ∃ s ∈ S, ∃ v, eval ι v s ≠ 1
  · obtain ⟨s, hs, v, hv⟩ := hS
    have hs₀ : V ι {s} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun u hu => hv (Subsingleton.elim v u ▸ mem_V.1 hu s rfl)
    refine ⟨{s}, Set.singleton_subset_iff.2 hs, Set.subsingleton_singleton, ?_⟩
    rw [hs₀, eq_comm, ← Set.subset_empty_iff, ← hs₀]
    exact V_antitone ι (Set.singleton_subset_iff.2 hs)
  · refine ⟨∅, Set.empty_subset S, Set.subsingleton_empty, ?_⟩
    simp only [not_exists, not_and, not_not] at hS
    rw [V_empty]
    exact (Set.eq_univ_of_forall fun v => mem_V.2 fun s hs => hS s hs v).symm

/-! ### Finitely generated commutative groups -/

section CommGroup

variable {H : Type*} [CommGroup H]

/-- If equations over `G` are recorded in a Noetherian `ℤ`-module `M` through `ψ`, in such a way
that each evaluation vanishes exactly on the kernel of an additive map out of `M`, then every
system is equivalent to a finite subsystem: finitely many of the vectors `ψ s`, `s ∈ S`, span the
same submodule as all of them. -/
private theorem exists_finite_V_eq_of_isNoetherian {ι : G →* H} {M A : Type*} [AddCommGroup M]
    [IsNoetherian ℤ M] [AddGroup A] (ψ : GX G X → M)
    (hψ : ∀ v : X → H, ∃ L : M →+ A, ∀ w, L (ψ w) = 0 ↔ eval ι v w = 1) (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  classical
  obtain ⟨T, hTS, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ψ '' S)).1
    (IsNoetherian.noetherian (Submodule.span ℤ (ψ '' S)))
  obtain ⟨S₀, hS₀, hfin, hspan⟩ := (Set.exists_subset_image_finite_and
    (p := fun t => Submodule.span ℤ t = Submodule.span ℤ (ψ '' S))).1
      ⟨(T : Set M), hTS, T.finite_toSet, hT.symm⟩
  refine ⟨S₀, hS₀, hfin, ?_⟩
  ext v
  obtain ⟨L, hL⟩ := hψ v
  have key (T : Set (GX G X)) :
      v ∈ V ι T ↔ Submodule.span ℤ (ψ '' T) ≤ L.ker.toIntSubmodule := by
    rw [Submodule.span_le, Set.image_subset_iff]
    simp [Set.subset_def, hL]
  rw [key, key, hspan]

/-- Finitely generated commutative groups are equationally Noetherian, over any coefficients.
At a point `v`, an equation `w` evaluates to `w(1) * ∏ₓ v x ^ nₓ(w)`, where `nₓ(w)` is the
exponent sum of the variable `x` in `w`; so a system is a system of linear equations whose
coefficient vectors `(w(1), n(w))` lie in the Noetherian `ℤ`-module `H × ℤⁿ`. -/
theorem isEquationallyNoetherian_of_commGroup_of_fg [Group.FG H] (ι : G →* H) :
    IsEquationallyNoetherian ι := by
  classical
  intro n S
  have : Module.Finite ℤ (Additive H) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 inferInstance)
  -- The exponent sum of the variable `x`.
  let e (x : Fin n) : GX G (Fin n) →* Multiplicative ℤ :=
    eval 1 fun y => if y = x then Multiplicative.ofAdd 1 else 1
  refine exists_finite_V_eq_of_isNoetherian
    (M := Additive H × (Fin n → ℤ)) (fun w => (Additive.ofMul (eval ι 1 w), fun x => (e x w).toAdd))
    (fun v => ⟨AddMonoidHom.fst _ _ + ∑ x, (zmultiplesHom _ (Additive.ofMul (v x))).comp
      ((Pi.evalAddMonoidHom (fun _ => ℤ) x).comp (AddMonoidHom.snd _ _)), fun w => ?_⟩) S
  have heval : eval ι v = eval ι 1 * ∏ x, (zpowersHom H (v x)).comp (e x) :=
    hom_ext (MonoidHom.ext fun _ => by simp [e])
      (FreeGroup.ext_hom _ _ fun y => by simp [e, apply_ite (zpowersHom H _)])
  rw [heval, ← ofMul_eq_zero]
  simp [ofMul_mul, ofMul_prod, ofMul_zpow]

/-- The infinite cyclic group is equationally Noetherian over itself. -/
theorem isEquationallyNoetherian_int :
    IsEquationallyNoetherian (MonoidHom.id (Multiplicative ℤ)) :=
  isEquationallyNoetherian_of_commGroup_of_fg _

end CommGroup

/-! ### A group which is not equationally Noetherian -/

/-- A direct product `κ → K` of infinitely many copies of a nonabelian group is not equationally
Noetherian over itself. If `a` and `b` do not commute, the one-variable system `[x, aᵢ] = 1`
(`i : κ`), where `aᵢ` is `a` in the coordinate `i` and `1` elsewhere, is equivalent to none of its
finite subsystems: for `j` outside the finitely many coordinates involved, `x = bⱼ` solves the
subsystem but not `[x, aⱼ] = 1`. -/
theorem not_isEquationallyNoetherian_pi {κ : Type*} [Infinite κ] {a b : K}
    (hab : ¬Commute a b) : ¬IsEquationallyNoetherian (MonoidHom.id (κ → K)) := by
  classical
  intro h
  -- `aᵢ`, and the equation `[x, aᵢ]`.
  let c (i : κ) : κ → K := Pi.mulSingle i a
  let w (i : κ) : GX (κ → K) Unit :=
    ⁅(inr (FreeGroup.of ()) : GX (κ → K) Unit), inl (c i)⁆
  have hw (u : κ → K) (i : κ) : eval (.id _) (fun _ => u) (w i) = ⁅u, c i⁆ := by
    simp [w, map_commutatorElement]
  obtain ⟨t, -, ht, htV⟩ := (Set.exists_subset_image_finite_and
    (p := fun T => V (.id _) T = V (.id (κ → K)) (w '' Set.univ))).1
      (h.exists_finite (w '' Set.univ))
  obtain ⟨j, hj⟩ := ht.exists_notMem
  have hmem : (fun _ => (Pi.mulSingle j b : κ → K)) ∈ V (.id _) (w '' t) := by
    refine mem_V.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hji : j ≠ i := by
      rintro rfl
      exact hj hi
    rw [hw, commutatorElement_eq_one_iff_commute]
    exact Pi.mulSingle_commute (f := fun _ : κ => K) hji b a
  rw [htV] at hmem
  have hj' := mem_V.1 hmem (w j) ⟨j, trivial, rfl⟩
  rw [hw, commutatorElement_eq_one_iff_commute] at hj'
  have hba := congrFun hj'.eq j
  simp only [c, Pi.mul_apply, Pi.mulSingle_eq_same] at hba
  exact hab hba.symm

end TauCeti.GroupAlgGeom
