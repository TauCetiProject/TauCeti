/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.RingTheory.Finiteness.Basic
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
homomorphism `G' →* G`. Finite groups are equationally Noetherian, and so are commutative groups
such as `ℤ`, because a system over a commutative group is a system of linear equations whose
exponent vectors span a finitely generated submodule of `ℤⁿ`. The property is not
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
  `TauCeti.GroupAlgGeom.isEquationallyNoetherian_of_commGroup`: finite groups and commutative
  groups are equationally Noetherian.
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

variable {G G' H K X : Type*} [Group G] [Group G'] [Group H] [Group K]

/-- `H` is equationally Noetherian over the coefficients `ι : G →* H` when every system of
equations `S ⊆ G[X]` in finitely many variables has a finite subsystem `S₀ ⊆ S` with the same
solutions in `H`. The variables are taken to be `Fin n`; see
`IsEquationallyNoetherian.exists_finite` for an arbitrary finite type of variables. -/
def IsEquationallyNoetherian (ι : G →* H) : Prop :=
  ∀ (n : ℕ) (S : Set (GX G (Fin n))), ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S

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

/-! ### Finite groups -/

/-- Finite groups are equationally Noetherian, over any coefficients. -/
theorem isEquationallyNoetherian_of_finite [Finite H] (ι : G →* H) :
    IsEquationallyNoetherian ι := fun _ S =>
  exists_finite_V_eq_of_finite S

/-! ### Commutative groups -/

section CommGroup

variable {H : Type*} [CommGroup H]

/-- If equations over `G` are recorded in a Noetherian `ℤ`-module `M` through `ψ`, in such a way
that any two evaluations agree exactly on the kernel of an additive map out of `M`, then every
system `S` is equivalent to a finite subsystem. Finitely many of the vectors `ψ s`, `s ∈ S`, span
the same submodule as all of them, so every equation of `S` is constant on the solutions of the
corresponding equations; either it is `1` there, or adding one equation leaves no solutions. -/
private theorem exists_finite_V_eq_of_isNoetherian {ι : G →* H} {M A : Type*} [AddCommGroup M]
    [IsNoetherian ℤ M] [AddGroup A] (ψ : GX G X → M)
    (hψ : ∀ u v : X → H, ∃ L : M →+ A, ∀ w, L (ψ w) = 0 ↔ eval ι u w = eval ι v w)
    (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  classical
  obtain ⟨T, hTS, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ψ '' S)).1
    (IsNoetherian.noetherian (Submodule.span ℤ (ψ '' S)))
  obtain ⟨S₁, hS₁, hfin, hspan⟩ := (Set.exists_subset_image_finite_and
    (p := fun t => Submodule.span ℤ t = Submodule.span ℤ (ψ '' S))).1
      ⟨(T : Set M), hTS, T.finite_toSet, hT.symm⟩
  -- Every equation of `S` takes the same value at any two solutions of `S₁`.
  have hconst {u v} (hu : u ∈ V ι S₁) (hv : v ∈ V ι S₁) {w} (hw : w ∈ S) :
      eval ι u w = eval ι v w := by
    obtain ⟨L, hL⟩ := hψ u v
    have hle : Submodule.span ℤ (ψ '' S₁) ≤ L.ker.toIntSubmodule := by
      rw [Submodule.span_le, Set.image_subset_iff]
      intro s hs
      simp [hL, mem_V.1 hu s hs, mem_V.1 hv s hs]
    exact (hL w).1 (hle (hspan ▸ Submodule.subset_span (Set.mem_image_of_mem ψ hw)))
  by_cases h : V ι S₁ ⊆ V ι S
  · exact ⟨S₁, hS₁, hfin, h.antisymm (V_antitone ι hS₁)⟩
  · obtain ⟨u, hu, huS⟩ := Set.not_subset.1 h
    obtain ⟨w, hw, hwu⟩ : ∃ w ∈ S, eval ι u w ≠ 1 := by simpa using huS
    have hsub : insert w S₁ ⊆ S := Set.insert_subset hw hS₁
    refine ⟨insert w S₁, hsub, hfin.insert w, (V_antitone ι hsub).antisymm' fun v hv => ?_⟩
    exact absurd ((hconst hu (V_antitone ι (Set.subset_insert w S₁) hv) hw).trans
      (mem_V.1 hv w (Set.mem_insert w S₁))) hwu

/-- Commutative groups are equationally Noetherian, over any coefficients. At a point `v`, an
equation `w` evaluates to `w(1) * ∏ₓ v x ^ nₓ(w)`, where `nₓ(w)` is the exponent sum of the
variable `x` in `w`; so two points give the same value on `w` exactly when the exponent vector
`n(w)`, which lies in the Noetherian `ℤ`-module `ℤⁿ`, is in the kernel of an additive map. -/
theorem isEquationallyNoetherian_of_commGroup (ι : G →* H) : IsEquationallyNoetherian ι := by
  classical
  intro n S
  -- The exponent sum of the variable `x`.
  let e (x : Fin n) : GX G (Fin n) →* Multiplicative ℤ :=
    eval 1 fun y => if y = x then Multiplicative.ofAdd 1 else 1
  have heval (v : Fin n → H) : eval ι v = eval ι 1 * ∏ x, (zpowersHom H (v x)).comp (e x) :=
    hom_ext (MonoidHom.ext fun _ => by simp [e])
      (FreeGroup.ext_hom _ _ fun y => by simp [e, apply_ite (zpowersHom H _)])
  refine exists_finite_V_eq_of_isNoetherian (A := Additive H) (fun w x => (e x w).toAdd)
    (fun u v => ⟨∑ x, (zmultiplesHom _ (Additive.ofMul (u x / v x))).comp
      (Pi.evalAddMonoidHom (fun _ => ℤ) x), fun w => ?_⟩) S
  calc _ ↔ ∏ x, (u x / v x) ^ (e x w).toAdd = 1 := by
        rw [← ofMul_eq_zero]
        simp [ofMul_prod, ofMul_zpow]
    _ ↔ _ := by
        rw [heval u, heval v]
        simp [div_zpow, Finset.prod_div_distrib, div_eq_one]

/-- The infinite cyclic group is equationally Noetherian over itself. -/
theorem isEquationallyNoetherian_int :
    IsEquationallyNoetherian (MonoidHom.id (Multiplicative ℤ)) :=
  isEquationallyNoetherian_of_commGroup _

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
