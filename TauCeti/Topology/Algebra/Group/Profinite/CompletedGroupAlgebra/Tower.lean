/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.QuotientTower
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# The completed group algebra along a tower of finite quotients

The completed group algebra `R[[Γ]]` is the inverse limit of the group algebras `R[Γ ⧸ U]` over
all open normal subgroups `U` of `Γ`. When the compact group `Γ` carries a tower of finite
quotients `q n : Γ → A n` (`TauCeti.FiniteQuotientTower`), the kernels of the levels are cofinal
among the open normal subgroups, so the countably many group algebras `R[A n]` already describe
`R[[Γ]]`. This file records the two halves of that description.

* Each level gives an `R`-algebra projection `towerProj R T n : R[[Γ]] → R[A n]`, the projection
  onto `R[Γ ⧸ ker q n]` read through the isomorphism `Γ ⧸ ker q n ≃ A n` induced by `q n`. The
  projections are compatible with the transition maps, the projection onto any `R[Γ ⧸ U]` factors
  through a level whose kernel lies in `U`, and an element of `R[[Γ]]`, or an algebra map into it,
  is determined by its tower projections.
* A family of `R`-algebra maps `f n : B → R[A n]`, compatible with the transition maps, assembles
  into an `R`-algebra map `towerLift T f hf : B → R[[Γ]]` whose tower projections are the `f n`.

This is the form in which coordinates on `R[[Γ]]` are usually built: for `Γ = ℤ_p` with its
congruence tower, a compatible family of maps into the group algebras `R[ℤ/pⁿ]` is a map into the
Iwasawa algebra `R[[ℤ_p]]`.

## Main definitions

* `TauCeti.completedGroupAlgebra.towerProj R T n`: the projection `R[[Γ]] →ₐ[R] R[A n]` onto the
  `n`-th level of the tower `T`.
* `TauCeti.completedGroupAlgebra.towerLift T f hf`: the `R`-algebra map into `R[[Γ]]` assembled
  from a compatible family `f n : B →ₐ[R] R[A n]`.

## Main results

* `TauCeti.completedGroupAlgebra.towerProj_of`: a group element projects to its image at the
  level.
* `TauCeti.completedGroupAlgebra.mapDomain_t_towerProj`: the projections are compatible with the
  transition maps.
* `TauCeti.completedGroupAlgebra.proj_eq_mapDomain_towerProj`: the projection onto `R[Γ ⧸ U]`
  factors through any level whose kernel lies in `U`.
* `TauCeti.completedGroupAlgebra.ext_towerProj`,
  `TauCeti.completedGroupAlgebra.algHom_ext_towerProj`: elements of `R[[Γ]]`, and algebra maps
  into it, are determined by their tower projections.
* `TauCeti.completedGroupAlgebra.towerProj_towerLift`,
  `TauCeti.completedGroupAlgebra.proj_towerLift`: the projections of `towerLift T f hf`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3, for completed group algebras as
  inverse limits over a cofinal system of open normal subgroups.
-/

public section

open MonoidAlgebra

namespace TauCeti.completedGroupAlgebra

variable (R : Type*) [CommRing R] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {A : ℕ → Type*}
  [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)]
  (T : FiniteQuotientTower Γ A)

/-- The projection of the completed group algebra onto the group algebra of the `n`-th level of a
tower of finite quotients: the projection onto `R[Γ ⧸ ker q n]` followed by the isomorphism
`Γ ⧸ ker q n ≃ A n` induced by `q n`. It sends a group element `γ` to `q n γ` (`towerProj_of`). -/
noncomputable def towerProj (n : ℕ) : completedGroupAlgebra R Γ →ₐ[R] MonoidAlgebra R (A n) :=
  (mapDomainAlgHom R R (_root_.QuotientGroup.lift (T.ker n : Subgroup Γ) (T.q n : Γ →* A n)
    (T.toSubgroup_ker n).le)).comp (proj R Γ (T.ker n))

variable {R T}

/-- The projection onto the `n`-th level of a tower sends a group element to its image at that
level. -/
@[simp]
theorem towerProj_of (n : ℕ) (γ : Γ) :
    towerProj R T n (of R Γ γ) = single (T.q n γ) 1 := by
  simp [towerProj]

/-- **The projection onto a finite quotient factors through a level of the tower.** If the
kernel of the `n`-th level lies in the open normal subgroup `U`, the projection onto `R[Γ ⧸ U]` is
the projection onto `R[A n]` followed by the map induced by `A n → Γ ⧸ U`. -/
theorem proj_eq_mapDomain_towerProj {n : ℕ} {U : OpenNormalSubgroup Γ} (h : T.ker n ≤ U)
    (x : completedGroupAlgebra R Γ) :
    proj R Γ U x = mapDomain (T.toQuotient (U := U.toSubgroup) h) (towerProj R T n x) := by
  rw [towerProj, AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_mapDomain,
    ← mapDomain_mapOfLE_proj h]
  congr 1
  funext y
  induction y using _root_.QuotientGroup.induction_on with
  | H g => simp

/-- **The tower projections are compatible with the transition maps**: for `m ≤ n`, the
projection onto `R[A n]` followed by the map induced by `A n → A m` is the projection onto
`R[A m]`. -/
@[simp]
theorem mapDomain_t_towerProj {m n : ℕ} (h : m ≤ n) (x : completedGroupAlgebra R Γ) :
    mapDomain (T.t h) (towerProj R T n x) = towerProj R T m x := by
  -- Both sides are recovered from the projection onto `R[Γ ⧸ ker q m]` through the injective map
  -- induced by `A m ≃ Γ ⧸ ker q m`.
  refine mapDomain_injective (T.toQuotient_injective m) ?_
  rw [← proj_eq_mapDomain_towerProj le_rfl, mapDomain_mapDomain,
    proj_eq_mapDomain_towerProj (T.ker_antitone h)]
  congr 1
  funext a
  exact T.toQuotient_t h _ a

/-- **An element of the completed group algebra of a compact group is determined by its tower
projections.** -/
theorem ext_towerProj [CompactSpace Γ] {x y : completedGroupAlgebra R Γ}
    (h : ∀ n, towerProj R T n x = towerProj R T n y) : x = y :=
  ext fun U ↦ by
    obtain ⟨n, hn⟩ := T.exists_ker_le_of_isOpen (U := U.toSubgroup) U.isOpen
    rw [proj_eq_mapDomain_towerProj (U := U) hn, proj_eq_mapDomain_towerProj (U := U) hn, h]

/-- Two `R`-algebra maps into the completed group algebra of a compact group with the same tower
projections are equal. -/
theorem algHom_ext_towerProj [CompactSpace Γ] {B : Type*} [Semiring B] [Algebra R B]
    {g₁ g₂ : B →ₐ[R] completedGroupAlgebra R Γ}
    (h : ∀ n, (towerProj R T n).comp g₁ = (towerProj R T n).comp g₂) : g₁ = g₂ :=
  AlgHom.ext fun b ↦ ext_towerProj fun n ↦ AlgHom.congr_fun (h n) b

section Lift

variable {B : Type*} [Semiring B] [Algebra R B] {f : ∀ n, B →ₐ[R] MonoidAlgebra R (A n)}
  (hf : ∀ ⦃m n : ℕ⦄ (h : m ≤ n) (b : B), mapDomain (T.t h) (f n b) = f m b)
include hf

/-- Pushing a compatible family forward to `R[Γ ⧸ U]` does not depend on the level used, among
those whose kernel lies in `U`. -/
private theorem mapDomain_toQuotient_eq {U : Subgroup Γ} [U.Normal] {m n : ℕ}
    (hm : (T.ker m : Subgroup Γ) ≤ U) (hn : (T.ker n : Subgroup Γ) ≤ U) (b : B) :
    mapDomain (T.toQuotient hm) (f m b) = mapDomain (T.toQuotient hn) (f n b) := by
  have key {m n : ℕ} (h : m ≤ n) (hm : (T.ker m : Subgroup Γ) ≤ U)
      (hn : (T.ker n : Subgroup Γ) ≤ U) :
      mapDomain (T.toQuotient hm) (f m b) = mapDomain (T.toQuotient hn) (f n b) := by
    rw [← hf h, mapDomain_mapDomain]
    congr 1
    funext a
    exact T.toQuotient_t h hm a
  rcases le_total m n with h | h
  · exact key h hm hn
  · exact (key h hn hm).symm

variable [CompactSpace Γ]

variable (T) in
/-- **The universal property of the completed group algebra along a tower.** A family of
`R`-algebra maps `f n : B →ₐ[R] R[A n]` into the levels of a tower of finite quotients of a compact
group `Γ`, compatible with the transition maps, assembles into an `R`-algebra map
`B →ₐ[R] R[[Γ]]` whose tower projections are the `f n` (`towerProj_towerLift`). It is the unique
such map (`algHom_ext_towerProj`). -/
noncomputable def towerLift : B →ₐ[R] completedGroupAlgebra R Γ :=
  lift R Γ (fun U ↦ (mapDomainAlgHom R R (T.toQuotient
      (T.exists_ker_le_of_isOpen (U := U.toSubgroup) U.isOpen).choose_spec)).comp
      (f (T.exists_ker_le_of_isOpen (U := U.toSubgroup) U.isOpen).choose))
    fun U V hUV b ↦ by
      simp only [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_mapDomain]
      rw [show (QuotientGroup.mapOfLE hUV ∘ T.toQuotient _) = T.toQuotient _ from
        funext (T.mapOfLE_toQuotient _ hUV)]
      exact mapDomain_toQuotient_eq hf _ _ b

/-- The projection of `towerLift T f hf` onto `R[Γ ⧸ U]` is `f n` followed by the map induced by
`A n → Γ ⧸ U`, for any level `n` whose kernel lies in `U`. -/
theorem proj_towerLift {n : ℕ} {U : OpenNormalSubgroup Γ} (h : T.ker n ≤ U) (b : B) :
    proj R Γ U (towerLift T hf b) = mapDomain (T.toQuotient (U := U.toSubgroup) h) (f n b) := by
  rw [towerLift, proj_lift, AlgHom.comp_apply, mapDomainAlgHom_apply]
  exact mapDomain_toQuotient_eq hf _ _ b

/-- **The tower projections of `towerLift T f hf` are the maps `f n`.** -/
@[simp]
theorem towerProj_towerLift (n : ℕ) (b : B) : towerProj R T n (towerLift T hf b) = f n b := by
  refine mapDomain_injective (T.toQuotient_injective n) ?_
  rw [← proj_eq_mapDomain_towerProj le_rfl, proj_towerLift hf le_rfl]

/-- The tower projections of `towerLift T f hf` are the maps `f n`, as algebra maps. -/
@[simp]
theorem towerProj_comp_towerLift (n : ℕ) : (towerProj R T n).comp (towerLift T hf) = f n :=
  AlgHom.ext (towerProj_towerLift hf n)

end Lift

end TauCeti.completedGroupAlgebra
