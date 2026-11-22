/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.Algebra.MonoidAlgebra.CharEval.Basic

/-!
# Character group rings

Let `O` be a commutative ring and `G` a commutative group. Collecting character evaluations
`MonoidHom.charEval` (`TauCeti.Algebra.MonoidAlgebra.CharEval.Basic`) at a set `Ψ` of characters
`G →* Oˣ` gives the joint evaluation `O[G] → ∏_{ψ ∈ Ψ} O`, whose image is the *character group
ring* `R_Ψ`: an `O`-subalgebra of the product, and a quotient of `O[G]` by the intersection of the
kernels of the evaluations at the members of `Ψ`.

Character group rings are the coefficient orders of the integral Brumer–Stark arguments of
Dasgupta and Kakde: they interpolate between `O` (`Ψ = {1}`) and, for `G` finite and `O` a
domain with enough roots of unity, `O[G]` itself (`Ψ` all characters). Under the same
hypotheses, the quotient `O[G] / N_I O[G]` by the norm element `N_I` of a subgroup `I` is the
character group ring of the set of characters that are nontrivial on `I` (Dasgupta–Kakde,
Lemma 2.2; proved in `TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Norm`). Character group rings are
in general proper suborders of the product `∏_{ψ ∈ Ψ} O`.

The main theorem is that the joint evaluation at all characters is injective when `G` is finite
and `O` is a domain with enough roots of unity (`Set.jointEval_injective`), so that the
character group ring of the set of all characters is `O[G]` itself.

## Main definitions

* `Set.jointEval`: the joint evaluation `O[G] →ₐ[O] (Ψ → O)` at a set of characters.
* `Set.charGroupRing`: the character group ring `R_Ψ`, the range of `Ψ.jointEval`.
* `Set.charGroupRing.proj`: the canonical surjection `α_Ψ : O[G] →ₐ[O] R_Ψ` onto the character
  group ring.
* `Set.charGroupRing.restrictAlgHom`: the canonical surjective transition homomorphism
  `R_Ψ →ₐ[O] R_{Ψ'}` for `Ψ' ⊆ Ψ`.
* `Set.charGroupRing.evalAlgHom`: coordinate evaluation `R_Ψ →ₐ[O] O` at `ψ ∈ Ψ`.
* `Set.charGroupRing.singletonAlgEquiv`: the canonical isomorphism `R_{{ψ}} ≃ₐ[O] O`.

## Main results

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

Declarations whose first explicit argument is a set of characters live in the `Set` namespace, so
that `Ψ.jointEval` and `Ψ.charGroupRing` elaborate by dot notation.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), §2.2.
* E. Artin, *Galois Theory*, Theorem 12, for the linear independence of characters.
-/

public section

section CommSemiring

variable {O G : Type*} [CommSemiring O] [CommGroup G]

namespace Set

/-- The joint evaluation `ev_Ψ : O[G] → ∏_{ψ ∈ Ψ} O`, `x ↦ (ψ(x))_{ψ ∈ Ψ}`, at a set `Ψ` of
characters of `G`. -/
noncomputable def jointEval (Ψ : Set (G →* Oˣ)) : MonoidAlgebra O G →ₐ[O] (Ψ → O) :=
  AlgHom.pi fun ψ ↦ ψ.val.charEval

/-- The `ψ`-coordinate of the joint evaluation is the evaluation at `ψ`. -/
@[simp]
theorem jointEval_apply (Ψ : Set (G →* Oˣ)) (x : MonoidAlgebra O G) (ψ : Ψ) :
    jointEval Ψ x ψ = ψ.val.charEval x :=
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
    y ∈ charGroupRing Ψ ↔ ∃ x : MonoidAlgebra O G, ∀ ψ : Ψ, ψ.val.charEval x = y ψ := by
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
    (proj Ψ x : Ψ → O) ψ = ψ.val.charEval x :=
  (rfl)

variable (Ψ) in
/-- The projection `α_Ψ` onto the character group ring is surjective. -/
theorem proj_surjective : Function.Surjective (proj Ψ) :=
  AlgHom.rangeRestrict_surjective _

variable (Ψ) in
/-- A character group ring of a finite group is a finite coefficient module. -/
instance [Finite G] : Module.Finite O (charGroupRing Ψ) :=
  Module.Finite.of_surjective (proj Ψ).toLinearMap (proj_surjective Ψ)

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

/-- For `Ψ' ⊆ Ψ`, restricting functions from `Ψ` to `Ψ'` defines the canonical surjective
`O`-algebra transition homomorphism `R_Ψ →ₐ[O] R_{Ψ'}` through which `α_{Ψ'}` factors. -/
noncomputable def restrictAlgHom {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) :
    Ψ.charGroupRing →ₐ[O] Ψ'.charGroupRing :=
  (AlgHom.pi fun ψ : Ψ' ↦
    (Pi.evalAlgHom O (fun _ : Ψ ↦ O) ⟨ψ.val, h ψ.property⟩).comp Ψ.charGroupRing.val).codRestrict
      Ψ'.charGroupRing fun y ↦ by
    obtain ⟨x, hx⟩ := mem_iff.mp y.property
    exact mem_iff.mpr ⟨x, fun ψ ↦ hx ⟨ψ.val, h ψ.property⟩⟩

/-- Coordinatewise formula for `restrictAlgHom`. -/
@[simp]
theorem coe_restrictAlgHom_apply {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ)
    (y : Ψ.charGroupRing) (ψ : Ψ') :
    (restrictAlgHom h y : Ψ' → O) ψ = (y : Ψ → O) ⟨ψ.val, h ψ.property⟩ := by
  simp [restrictAlgHom]

/-- Restricting a character group ring to itself is the identity algebra homomorphism. -/
@[simp]
theorem restrictAlgHom_self (h : Ψ ⊆ Ψ) :
    restrictAlgHom h = AlgHom.id O Ψ.charGroupRing := by
  ext y ψ
  simp

/-- Iterated restriction along `Ψ'' ⊆ Ψ' ⊆ Ψ` agrees with restriction along `Ψ'' ⊆ Ψ`. -/
@[simp]
theorem restrictAlgHom_restrictAlgHom {Ψ'' Ψ' Ψ : Set (G →* Oˣ)}
    (h₁ : Ψ'' ⊆ Ψ') (h₂ : Ψ' ⊆ Ψ) (y : Ψ.charGroupRing) :
    restrictAlgHom h₁ (restrictAlgHom h₂ y) = restrictAlgHom (h₁.trans h₂) y := by
  ext ψ
  simp

/-- Composition of transition homomorphisms `restrictAlgHom`. -/
@[simp]
theorem restrictAlgHom_comp {Ψ'' Ψ' Ψ : Set (G →* Oˣ)}
    (h₁ : Ψ'' ⊆ Ψ') (h₂ : Ψ' ⊆ Ψ) :
    (restrictAlgHom h₁).comp (restrictAlgHom h₂) = restrictAlgHom (h₁.trans h₂) :=
  AlgHom.ext (restrictAlgHom_restrictAlgHom h₁ h₂)

/-- `restrictAlgHom` commutes with the canonical projections `α_Ψ` and `α_{Ψ'}`. -/
@[simp]
theorem restrictAlgHom_proj {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) (x : MonoidAlgebra O G) :
    restrictAlgHom h (proj Ψ x) = proj Ψ' x := by
  ext ψ
  simp

/-- Composing `restrictAlgHom` with `proj Ψ` recovers `proj Ψ'`. -/
@[simp]
theorem restrictAlgHom_comp_proj {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) :
    (restrictAlgHom h).comp (proj Ψ) = proj Ψ' :=
  AlgHom.ext (restrictAlgHom_proj h)

/-- `restrictAlgHom` is surjective whenever `Ψ' ⊆ Ψ`. -/
theorem restrictAlgHom_surjective {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) :
    Function.Surjective (restrictAlgHom h) := fun y ↦ by
  obtain ⟨x, rfl⟩ := proj_surjective Ψ' y
  exact ⟨proj Ψ x, restrictAlgHom_proj h x⟩

/-- Evaluation of `R_Ψ` at a member `ψ ∈ Ψ`: the surjective `O`-algebra homomorphism `R_Ψ →ₐ[O] O`
projecting onto the `ψ`-coordinate. -/
noncomputable def evalAlgHom {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) : Ψ.charGroupRing →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : Ψ ↦ O) ⟨ψ, hψ⟩).comp Ψ.charGroupRing.val

/-- `evalAlgHom` reads off the `ψ`-coordinate in `Ψ → O`. -/
@[simp]
theorem evalAlgHom_apply {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) (y : Ψ.charGroupRing) :
    evalAlgHom hψ y = (y : Ψ → O) ⟨ψ, hψ⟩ := by
  simp [evalAlgHom]

/-- Composing `evalAlgHom` with `α_Ψ : O[G] → R_Ψ` recovers `ψ.charEval`. -/
theorem evalAlgHom_proj {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) (x : MonoidAlgebra O G) :
    evalAlgHom hψ (proj Ψ x) = ψ.charEval x := by
  simp

/-- Composing `evalAlgHom` with `proj Ψ` gives `ψ.charEval`. -/
@[simp]
theorem evalAlgHom_comp_proj {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    (evalAlgHom hψ).comp (proj Ψ) = ψ.charEval :=
  AlgHom.ext (evalAlgHom_proj hψ)

/-- Composing `evalAlgHom` on `R_{Ψ'}` with `restrictAlgHom` recovers `evalAlgHom` on `R_Ψ`. -/
@[simp]
theorem evalAlgHom_comp_restrictAlgHom {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ)
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ') :
    (evalAlgHom hψ).comp (restrictAlgHom h) = evalAlgHom (h hψ) :=
  AlgHom.ext fun y ↦ by simp

/-- Coordinate evaluation `R_Ψ →ₐ[O] O` at any `ψ ∈ Ψ` is surjective, split by
`algebraMap O R_Ψ`. -/
theorem evalAlgHom_surjective {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    Function.Surjective (evalAlgHom hψ) :=
  fun a ↦ ⟨algebraMap O Ψ.charGroupRing a, (evalAlgHom hψ).commutes a⟩

/-- A nontrivial character group ring `R_Ψ` is necessarily indexed by a nonempty set `Ψ`, since
`∅ → O` is a subsingleton. -/
theorem nonempty_of_nontrivial [Nontrivial Ψ.charGroupRing] : Ψ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  subst h
  exact zero_ne_one
    (ext (y := (0 : (∅ : Set (G →* Oˣ)).charGroupRing)) fun ψ ↦ False.elim ψ.property)

/-- When `Ψ` is nonempty, `algebraMap O R_Ψ` is a local homomorphism because it has a left inverse
`evalAlgHom hψ`. -/
instance [Nonempty Ψ] : IsLocalHom (algebraMap O Ψ.charGroupRing) := by
  obtain ⟨ψ, hψ⟩ := ‹Nonempty Ψ›
  exact isLocalHom_of_leftInverse (evalAlgHom hψ) (fun a ↦ (evalAlgHom hψ).commutes a)

/-- When `R_Ψ` is nontrivial, `Ψ` is nonempty and hence `algebraMap O R_Ψ` is a local
homomorphism. -/
instance [Nontrivial Ψ.charGroupRing] : IsLocalHom (algebraMap O Ψ.charGroupRing) := by
  have := (nonempty_of_nontrivial (Ψ := Ψ)).to_subtype
  infer_instance

/-- The character group ring of a singleton `{ψ}` is canonically isomorphic to `O`. -/
noncomputable def singletonAlgEquiv (ψ : G →* Oˣ) : ({ψ} : Set (G →* Oˣ)).charGroupRing ≃ₐ[O] O :=
  AlgEquiv.ofAlgHom
    (evalAlgHom (Set.mem_singleton ψ))
    (Algebra.ofId O _)
    (AlgHom.ext fun a ↦ (evalAlgHom (Set.mem_singleton ψ)).commutes a)
    (AlgHom.ext fun y ↦ ext fun ⟨χ, hχ⟩ ↦ by
      cases Set.mem_singleton_iff.mp hχ
      simp)

/-- `singletonAlgEquiv` evaluates at `ψ`. -/
@[simp]
theorem singletonAlgEquiv_apply (ψ : G →* Oˣ) (y : ({ψ} : Set (G →* Oˣ)).charGroupRing) :
    singletonAlgEquiv ψ y = (y : ({ψ} : Set (G →* Oˣ)) → O) ⟨ψ, Set.mem_singleton ψ⟩ := by
  simp [singletonAlgEquiv]

/-- The inverse of `singletonAlgEquiv` is `algebraMap O R_{{ψ}}`. -/
@[simp]
theorem singletonAlgEquiv_symm_apply (ψ : G →* Oˣ) (a : O) :
    (singletonAlgEquiv ψ).symm a = algebraMap O ({ψ} : Set (G →* Oˣ)).charGroupRing a := by
  simp [singletonAlgEquiv]

/-- `singletonAlgEquiv` sends `α_{{ψ}}(x)` to `ψ(x)`. -/
theorem singletonAlgEquiv_proj (ψ : G →* Oˣ) (x : MonoidAlgebra O G) :
    singletonAlgEquiv ψ (proj {ψ} x) = ψ.charEval x := by
  simp

end charGroupRing

end Set

end CommSemiring

section Domain

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

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
