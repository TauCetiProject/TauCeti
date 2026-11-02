/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum

/-!
# Evaluation of a group ring at characters, and character group rings

Let `O` be a commutative ring and `G` a commutative group. A *character* of `G` is a group
homomorphism `ψ : G →* Oˣ`, and evaluation at `ψ` is the `O`-algebra homomorphism
`ψ : O[G] → O`, `∑ a_g g ↦ ∑ a_g ψ(g)`. Collecting the evaluations at a set `Ψ` of characters
gives the joint evaluation `O[G] → ∏_{ψ ∈ Ψ} O`, whose image is the *character group ring*
`R_Ψ`: an `O`-subalgebra of the product, and a quotient of `O[G]` by the intersection of the
kernels of the evaluations at the members of `Ψ`.

Character group rings are the coefficient orders of the integral Brumer–Stark arguments of
Dasgupta and Kakde: they interpolate between `O` (`Ψ = {1}`) and, for `G` finite and `O` a
domain with enough roots of unity, `O[G]` itself (`Ψ` all characters). Under the same
hypotheses, the quotient `O[G] / N_I O[G]` by the norm element `N_I` of a subgroup `I` is the
character group ring of the set of characters that are nontrivial on `I` (Dasgupta–Kakde,
Lemma 2.2); this identification is not proved in this file. Character group rings are in
general proper suborders of the product `∏_{ψ ∈ Ψ} O`.

The main theorem is that the joint evaluation at all characters is injective when `G` is finite
and `O` is a domain with enough roots of unity (`Set.jointEval_injective`), so that the
character group ring of the set of all characters is `O[G]` itself.

## Main definitions

* `MonoidHom.charEval`: evaluation `O[G] →ₐ[O] O` at a character, the `O[G]`-point
  `TauCeti.DiagonalizableGroup.point` of the diagonalizable group with values in `O`.
* `Set.jointEval`: the joint evaluation `O[G] →ₐ[O] (Ψ → O)` at a set of characters.
* `Set.charGroupRing`: the character group ring `R_Ψ`, the range of `Ψ.jointEval`.
* `Set.charGroupRing.proj`: the canonical surjection `α_Ψ : O[G] →ₐ[O] R_Ψ`.

## Main results

* `MonoidAlgebra.charEval_one_apply` and `MonoidHom.charEval_one`: the trivial character
  evaluates by the augmentation.
* `MonoidHom.charEval_subgroupCharSum_of_le_ker` and
  `MonoidHom.charEval_subgroupCharSum_eq_zero`: the evaluation of a character sum over a finite
  subgroup `H`, which is `#H` or `0` (row orthogonality); the norm element `∑_{h ∈ H} h` is the
  case of the trivial character.
* `TauCeti.eq_of_forall_charEval_eq` and `Set.jointEval_injective`: for `G` finite and `O` a
  domain with enough roots of unity, an element of `O[G]` is determined by its values at all
  characters.
* `Set.charGroupRing.proj_eq_proj_iff` and `Set.charGroupRing.ker_proj`: the kernel of
  `α_Ψ` is the intersection of the kernels of the evaluations at the members of `Ψ`.

## Implementation notes

Injectivity of the joint evaluation is not proved by inverting the character table, which would
first require showing that the order of `G` is nonzero in `O`. Instead, the functions
`ψ ↦ ψ(g)` are pairwise distinct characters of the character group, hence linearly independent
by Artin's theorem `linearIndependent_monoidHom`, and the joint evaluation sends the standard
basis of `O[G]` to them.

Declarations whose first explicit argument is a character or a set of characters live in the
`MonoidHom` and `Set` namespaces, so that `ψ.charEval`, `Ψ.jointEval` and `Ψ.charGroupRing`
elaborate by dot notation.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), §2.2.
* E. Artin, *Galois Theory*, Theorem 12, for the linear independence of characters.
-/

public section

section CommSemiring

variable {O G : Type*} [CommSemiring O] [CommGroup G]

/-- Evaluation of the group ring `O[G]` at a character `ψ : G →* Oˣ`: the `O`-algebra
homomorphism `∑ a_g g ↦ ∑ a_g ψ(g)`. It is the `O[G]`-point of the diagonalizable group
`D(G)` with values in `O` attached to `ψ`, and following Dasgupta–Kakde it is written `ψ(x)`
for `x ∈ O[G]`. Being reducible, it inherits the value lemmas of
`TauCeti.DiagonalizableGroup.point`: `TauCeti.DiagonalizableGroup.point_single` sends
`single g a` to `a • ψ g`, and `TauCeti.DiagonalizableGroup.point_single_one` sends `single g 1`
to `ψ g`. -/
noncomputable abbrev MonoidHom.charEval (ψ : G →* Oˣ) : MonoidAlgebra O G →ₐ[O] O :=
  TauCeti.DiagonalizableGroup.point ψ

/-- The trivial character evaluates by the coefficient-sum augmentation. -/
@[simp]
theorem MonoidAlgebra.charEval_one_apply (x : MonoidAlgebra O G) :
    (1 : G →* Oˣ).charEval x = TauCeti.MonoidAlgebra.augmentation O G x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single g a => simp

namespace MonoidHom

/-- As a ring homomorphism, evaluation at the trivial character is the coefficient-sum
augmentation. -/
theorem charEval_one :
    ((1 : G →* Oˣ).charEval : MonoidAlgebra O G →+* O) =
      TauCeti.MonoidAlgebra.augmentation O G :=
  RingHom.ext MonoidAlgebra.charEval_one_apply

/-- The value of a character `ψ` on the character sum `∑_{h ∈ H} χ(h) h` over a finite subgroup
`H` is `#H` when `χ ψ` is trivial on `H`. -/
theorem charEval_subgroupCharSum_of_le_ker (χ ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : H ≤ (χ * ψ).ker) :
    ψ.charEval (TauCeti.subgroupCharSum ((Units.coeHom O).comp χ) H) = Nat.card H := by
  have h (h : H) : ((χ h : Oˣ) : O) * ψ h = 1 := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hH h.2, Units.val_one]
  simp [TauCeti.subgroupCharSum_def, map_sum, h, Nat.card_eq_fintype_card]

/-- The norm element `∑_{h ∈ H} h` of a finite subgroup `H` on which `ψ` is trivial evaluates
to `#H` at `ψ`. -/
theorem charEval_subgroupCharSum_one_of_le_ker (ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : H ≤ ψ.ker) :
    ψ.charEval (TauCeti.subgroupCharSum (1 : G →* O) H) = Nat.card H := by
  simpa using charEval_subgroupCharSum_of_le_ker 1 ψ H
    fun g hg ↦ by simpa [MonoidHom.mem_ker] using hH hg

end MonoidHom

namespace Set

/-- The joint evaluation `ev_Ψ : O[G] → ∏_{ψ ∈ Ψ} O`, `x ↦ (ψ(x))_{ψ ∈ Ψ}`, at a set `Ψ` of
characters of `G`. -/
noncomputable def jointEval (Ψ : Set (G →* Oˣ)) : MonoidAlgebra O G →ₐ[O] (Ψ → O) :=
  AlgHom.pi fun ψ ↦ ψ.1.charEval

/-- The `ψ`-coordinate of the joint evaluation is the evaluation at `ψ`. -/
@[simp]
theorem jointEval_apply (Ψ : Set (G →* Oˣ)) (x : MonoidAlgebra O G) (ψ : Ψ) :
    jointEval Ψ x ψ = ψ.1.charEval x :=
  (rfl)

/-- The *character group ring* `R_Ψ` of a set `Ψ` of characters of `G`: the image of the joint
evaluation `O[G] → ∏_{ψ ∈ Ψ} O`, an `O`-subalgebra of the product. When `O` is a commutative
ring, it is equivalently the quotient of `O[G]` by the intersection of the kernels of the
evaluations at the members of `Ψ` (`Set.charGroupRing.ker_proj`). It is in general a proper
suborder of the product. -/
noncomputable def charGroupRing (Ψ : Set (G →* Oˣ)) : Subalgebra O (Ψ → O) :=
  (jointEval Ψ).range

/-- The character group ring is the range of the joint evaluation. -/
theorem charGroupRing_def (Ψ : Set (G →* Oˣ)) : charGroupRing Ψ = (jointEval Ψ).range :=
  (rfl)

namespace charGroupRing

variable {Ψ : Set (G →* Oˣ)}

/-- A function on `Ψ` lies in the character group ring exactly when it is the family of values
of some element of `O[G]` at the members of `Ψ`. -/
theorem mem_iff {y : Ψ → O} :
    y ∈ charGroupRing Ψ ↔ ∃ x : MonoidAlgebra O G, ∀ ψ : Ψ, ψ.1.charEval x = y ψ := by
  simp [charGroupRing, funext_iff]

/-- Two elements of the character group ring are equal when all their `ψ`-coordinates are. -/
@[ext]
theorem ext {y z : charGroupRing Ψ} (h : ∀ ψ : Ψ, (y : Ψ → O) ψ = (z : Ψ → O) ψ) : y = z :=
  Subtype.ext (funext h)

variable (Ψ) in
/-- The canonical surjection `α_Ψ : O[G] →ₐ[O] R_Ψ` onto the character group ring. -/
noncomputable def proj : MonoidAlgebra O G →ₐ[O] charGroupRing Ψ :=
  (jointEval Ψ).rangeRestrict

/-- The `ψ`-coordinate of `α_Ψ(x)` is `ψ(x)`. -/
@[simp]
theorem coe_proj_apply (x : MonoidAlgebra O G) (ψ : Ψ) :
    (proj Ψ x : Ψ → O) ψ = ψ.1.charEval x :=
  (rfl)

variable (Ψ) in
/-- The projection `α_Ψ` onto the character group ring is surjective. -/
theorem proj_surjective : Function.Surjective (proj Ψ) :=
  AlgHom.rangeRestrict_surjective _

/-- Two elements of `O[G]` have the same image in `R_Ψ` exactly when they have the same value at
every member of `Ψ`. -/
theorem proj_eq_proj_iff {x y : MonoidAlgebra O G} :
    proj Ψ x = proj Ψ y ↔ ∀ ψ ∈ Ψ, ψ.charEval x = ψ.charEval y := by
  simp [charGroupRing.ext_iff]

/-- The kernel criterion: `α_Ψ(x) = 0` exactly when `ψ(x) = 0` for every `ψ ∈ Ψ`. -/
theorem proj_eq_zero_iff {x : MonoidAlgebra O G} :
    proj Ψ x = 0 ↔ ∀ ψ ∈ Ψ, ψ.charEval x = 0 := by
  simpa using proj_eq_proj_iff (Ψ := Ψ) (x := x) (y := 0)

variable (Ψ) in
/-- The kernel of `α_Ψ : O[G] → R_Ψ` is the intersection of the kernels of the evaluations at the
members of `Ψ`. When `O` is a commutative ring, this gives `R_Ψ ≅ O[G] / ⋂_{ψ ∈ Ψ} ker ψ`. -/
theorem ker_proj : RingHom.ker (proj Ψ) = ⨅ ψ ∈ Ψ, RingHom.ker ψ.charEval := by
  ext x
  simp [RingHom.mem_ker, proj_eq_zero_iff]

end charGroupRing

end Set

end CommSemiring

section Domain

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

namespace MonoidHom

/-- Row orthogonality: the value of a character `ψ` on the character sum `∑_{h ∈ H} χ(h) h` over
a finite subgroup `H` vanishes when `χ ψ` is nontrivial on `H` and `O` is a domain. -/
theorem charEval_subgroupCharSum_eq_zero (χ ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : ¬ H ≤ (χ * ψ).ker) :
    ψ.charEval (TauCeti.subgroupCharSum ((Units.coeHom O).comp χ) H) = 0 := by
  have hne : (Units.coeHom O).comp ((χ * ψ).comp H.subtype) ≠ 1 := by
    intro h
    refine hH fun g hg ↦ Units.val_eq_one.mp ?_
    simpa using DFunLike.congr_fun h ⟨g, hg⟩
  simpa [TauCeti.subgroupCharSum_def, map_sum] using sum_hom_units_eq_zero _ hne

/-- The norm element `∑_{h ∈ H} h` of a finite subgroup `H` on which `ψ` is nontrivial evaluates
to `0` at `ψ` when `O` is a domain. For `H = G` this is the vanishing of a nontrivial character
on the group sum. -/
theorem charEval_subgroupCharSum_one_eq_zero (ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : ¬ H ≤ ψ.ker) :
    ψ.charEval (TauCeti.subgroupCharSum (1 : G →* O) H) = 0 := by
  simpa using charEval_subgroupCharSum_eq_zero 1 ψ H
    fun h ↦ hH fun g hg ↦ by simpa [MonoidHom.mem_ker] using h hg

end MonoidHom

variable [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- For a finite commutative group `G` and a domain `O` with enough roots of unity, an element
of `O[G]` is determined by its values at all characters `G →* Oˣ`. -/
theorem TauCeti.eq_of_forall_charEval_eq {x y : MonoidAlgebra O G}
    (h : ∀ ψ : G →* Oˣ, ψ.charEval x = ψ.charEval y) : x = y := by
  -- The functions `ψ ↦ ψ(g)` are pairwise distinct characters of the character group.
  let e : G → (G →* Oˣ) →* O := fun g ↦ (Units.coeHom O).comp (MonoidHom.eval g)
  have he : Function.Injective e := fun g g' hgg' ↦
    (CommGroup.forall_apply_eq_apply_iff G).mp fun ψ ↦ Units.ext (DFunLike.congr_fun hgg' ψ)
  -- The family of evaluations sends the standard basis of `O[G]` to these characters.
  let L : MonoidAlgebra O G →ₗ[O] (G →* Oˣ) → O := LinearMap.pi fun ψ ↦ ψ.charEval.toLinearMap
  have hL : Function.Injective L := by
    refine LinearMap.injective_of_linearIndependent (MonoidAlgebra.basis G O).span_eq ?_
    convert (linearIndependent_monoidHom (G →* Oˣ) O).comp e he using 1
    ext g ψ
    simp [L, e]
  exact hL (funext h)

/-- **The joint evaluation at all characters is injective**: for a finite commutative group `G`
and a domain `O` with enough roots of unity, `ev_Ψ : O[G] → ∏_{ψ ∈ Ψ} O` with `Ψ = univ` is
injective. -/
theorem Set.jointEval_injective :
    Function.Injective (jointEval (Set.univ : Set (G →* Oˣ))) := fun _ _ h ↦
  TauCeti.eq_of_forall_charEval_eq fun ψ ↦ by
    simpa using congr_fun h ⟨ψ, Set.mem_univ ψ⟩

/-- For a finite commutative group `G` and a domain `O` with enough roots of unity, the character
group ring of the set of all characters is `O[G]` itself: `α_Ψ` with `Ψ = univ` is bijective. -/
theorem Set.charGroupRing.proj_univ_bijective :
    Function.Bijective (proj (Set.univ : Set (G →* Oˣ))) :=
  ⟨fun _ _ h ↦ Set.jointEval_injective (congr_arg Subtype.val h), proj_surjective _⟩

end Domain
