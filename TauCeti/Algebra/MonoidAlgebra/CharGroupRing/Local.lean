/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Component
public import TauCeti.RingTheory.AdicCompletion.Finite
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Units, locality, and adic completeness of character group rings

Let `O` be a commutative ring, `G` a commutative group, and `Ψ` a set of characters `G →* Oˣ` with
character group ring `R_Ψ ⊆ ∏_{ψ ∈ Ψ} O`. Following Dasgupta and Kakde (§2.3, §5.1, §7.1, §7.2.9),
this file determines the units of `R_Ψ`, establishes when `R_Ψ` is a local ring, describes its
maximal ideal and residue field, and equips it with its complete Noetherian local `O`-algebra
structure:

* **Units (`Set.charGroupRing.isUnit_iff`, `Set.charGroupRing.isUnit_iff_isUnit_prod`)**: when `Ψ`
  is finite, `y ∈ R_Ψ` is a unit in `R_Ψ` (not merely in the ambient product `∏_{ψ ∈ Ψ} O`) if and
  only if every coordinate `y(ψ)` is a unit in `O`, equivalently if and only if `∏_{ψ ∈ Ψ} y(ψ)` is
  a unit in `O`. Indeed `y` is a root of the monic polynomial `P(X) = ∏_{ψ ∈ Ψ} (X - y(ψ)) ∈ O[X]`,
  whose constant term `± ∏_{ψ ∈ Ψ} y(ψ)` lies in `O ∩ (y) R_Ψ` by
  `Ideal.coeff_zero_mem_comap_of_root_mem`.
* **Locality (`Set.charGroupRing.isLocalRing`)**: suppose `(O, 𝔪)` is a local ring whose residue
  field has exponential characteristic `p` (`[ExpChar (ResidueField O) p]`, covering residue
  characteristic `p` for any prime `p`), and `Ψ` is finite, nonempty, and satisfies the `p`-power
  congruence condition `∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁(g)^{p^k} = ψ₂(g)^{p^k}`. Because
  `ResidueField O` is reduced of exponential characteristic `p`, all members of `Ψ` induce the same
  homomorphism `R_Ψ → ResidueField O` modulo `𝔪`. Hence coordinate evaluation `evalAlgHom : R_Ψ → O`
  at any `ψ ∈ Ψ` is a local homomorphism (`Set.charGroupRing.isLocalHom_evalAlgHom`), so `R_Ψ` is a
  local ring!
* **Consequences of locality**: once `[IsLocalRing Ψ.charGroupRing]` holds (for any local ring `O`,
  with no finiteness or `p`-power hypotheses repeated), surjectivity of `evalAlgHom` makes every
  coordinate evaluation a local homomorphism, identifying the maximal ideal of `R_Ψ` as the preimage
  of `𝔪` at any single `ψ ∈ Ψ` (`Set.charGroupRing.maximalIdeal_eq_comap`), showing `y ∈ R_Ψ` is a
  unit iff `y(ψ) ∈ Oˣ` at a single `ψ ∈ Ψ`
  (`Set.charGroupRing.isUnit_iff_isUnit_eval_of_isLocalRing`), identifying the residue field of
  `R_Ψ` with `ResidueField O` (`Set.charGroupRing.residueFieldEquiv`), and bounding some positive
  power of `𝔪_{R_Ψ}` inside `𝔪 R_Ψ` (`Set.charGroupRing.exists_maximalIdeal_pow_le_map`,
  Dasgupta–Kakde §7.2.9). When `O` is
  a complete Noetherian local ring, `R_Ψ` is automatically Noetherian and `𝔪_{R_Ψ}`-adically
  complete.
* **Component specialization (`Set.charGroupRing.isLocalRing_of_subset_component`)**: when `P` and
  `H` are complementary subgroups of `G` with `P` a `p`-group (`IsPGroup p P`, e.g. `G = G_p × G'`),
  any two characters of `G` agreeing on `H` have `p`-power-equal values everywhere on `G`, so every
  finite nonempty subset `Ψ ⊆ Ψ_χ` yields a local character group ring `R_Ψ`.

## Main definitions and results

* `Set.charGroupRing.evalAlgHom`: coordinate evaluation `R_Ψ →ₐ[O] O` at `ψ ∈ Ψ`.
* `Set.charGroupRing.singletonAlgEquiv`: `R_{ψ} ≃ₐ[O] O` for a single character `ψ`.
* `Set.charGroupRing.isUnit_iff` and `Set.charGroupRing.isUnit_iff_isUnit_prod`: unit criteria in
  `R_Ψ` for finite `Ψ`.
* `Set.charGroupRing.isLocalHom_evalAlgHom` and `Set.charGroupRing.isLocalRing`: locality of `R_Ψ`
  under `p`-power character congruence.
* `Set.charGroupRing.maximalIdeal_eq_comap`, `Set.charGroupRing.residueFieldEquiv`, and
  `Set.charGroupRing.exists_maximalIdeal_pow_le_map`: maximal ideal, residue field, and maximal
  ideal power containment `𝔪_{R_Ψ}^N ⊆ 𝔪 R_Ψ`.
* `Set.charGroupRing.isLocalRing_of_subset_component`, `Set.charGroupRing.nonempty_componentSet`,
  and `Set.charGroupRing.nonempty_componentNormSet`: specialization to subsets of a `χ`-component
  for `G = P × H` with `P` a `p`-group.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), §2.3 (p. 18),
  §5.1 (p. 43), §7.1 (p. 59), and §7.2.9 (p. 72).
-/

public section

namespace Set.charGroupRing

section EvalAndUnits

variable {O G : Type*} [CommSemiring O] [CommGroup G] {Ψ : Set (G →* Oˣ)}

/-- Evaluation of `R_Ψ` at a member `ψ ∈ Ψ`: the surjective `O`-algebra homomorphism `R_Ψ →ₐ[O] O`
projecting onto the `ψ`-coordinate. -/
noncomputable def evalAlgHom {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) : Ψ.charGroupRing →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : Ψ ↦ O) ⟨ψ, hψ⟩).comp Ψ.charGroupRing.val

/-- `evalAlgHom` reads off the `ψ`-coordinate in `Ψ → O`. -/
@[simp]
theorem evalAlgHom_apply {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) (y : Ψ.charGroupRing) :
    evalAlgHom hψ y = (y : Ψ → O) ⟨ψ, hψ⟩ :=
  (rfl)

/-- Composing `evalAlgHom` with `α_Ψ : O[G] → R_Ψ` recovers `ψ.charEval`. -/
theorem evalAlgHom_proj {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) (x : MonoidAlgebra O G) :
    evalAlgHom hψ (proj Ψ x) = ψ.charEval x :=
  coe_proj_apply x ⟨ψ, hψ⟩

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
  exact zero_ne_one (ext (y := (0 : (∅ : Set (G →* Oˣ)).charGroupRing)) fun ψ ↦ False.elim ψ.2)

/-- When `Ψ` is nonempty, `algebraMap O R_Ψ` is a local homomorphism because it has a left inverse
`evalAlgHom hψ`. -/
instance [Nonempty Ψ] : IsLocalHom (algebraMap O Ψ.charGroupRing) := by
  obtain ⟨ψ, hψ⟩ := ‹Nonempty Ψ›
  refine ⟨fun a ha ↦ ?_⟩
  simpa [(evalAlgHom hψ).commutes a] using ha.map (evalAlgHom hψ)

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
      rfl)

/-- `singletonAlgEquiv` evaluates at `ψ`. -/
@[simp]
theorem singletonAlgEquiv_apply (ψ : G →* Oˣ) (y : ({ψ} : Set (G →* Oˣ)).charGroupRing) :
    singletonAlgEquiv ψ y = (y : ({ψ} : Set (G →* Oˣ)) → O) ⟨ψ, Set.mem_singleton ψ⟩ :=
  (rfl)

/-- The inverse of `singletonAlgEquiv` is `algebraMap O R_{{ψ}}`. -/
@[simp]
theorem singletonAlgEquiv_symm_apply (ψ : G →* Oˣ) (a : O) :
    (singletonAlgEquiv ψ).symm a = algebraMap O ({ψ} : Set (G →* Oˣ)).charGroupRing a :=
  (rfl)

/-- `singletonAlgEquiv` sends `α_{{ψ}}(x)` to `ψ(x)`. -/
theorem singletonAlgEquiv_proj (ψ : G →* Oˣ) (x : MonoidAlgebra O G) :
    singletonAlgEquiv ψ (proj {ψ} x) = ψ.charEval x :=
  coe_proj_apply x ⟨ψ, Set.mem_singleton ψ⟩

end EvalAndUnits

section Units

variable {O G : Type*} [CommRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)} [Finite Ψ]

/-- **Units of a character group ring**: for a finite set `Ψ` of characters, an element `y ∈ R_Ψ`
is a unit in `R_Ψ` if and only if every coordinate `y(ψ)` is a unit in `O`. -/
theorem isUnit_iff {y : Ψ.charGroupRing} :
    IsUnit y ↔ ∀ ψ : Ψ, IsUnit ((y : Ψ → O) ψ) := by
  classical
  let := Fintype.ofFinite Ψ
  refine ⟨fun hy ψ ↦ hy.map (evalAlgHom ψ.2), fun hy ↦ ?_⟩
  let P : Polynomial O := ∏ ψ : Ψ, (Polynomial.X - Polynomial.C ((y : Ψ → O) ψ))
  have hroot : P.eval₂ (algebraMap O Ψ.charGroupRing) y = 0 := by
    rw [← Polynomial.aeval_def]
    refine ext fun χ ↦ ?_
    rw [← evalAlgHom_apply χ.2, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval,
      evalAlgHom_apply, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ χ) (by simp)
  have hP0_mem : P.coeff 0 ∈ (Ideal.span {y}).comap (algebraMap O Ψ.charGroupRing) :=
    Ideal.coeff_zero_mem_comap_of_root_mem (Ideal.mem_span_singleton_self y) hroot
  have hP0_unit : IsUnit (P.coeff 0) := by
    rw [← Polynomial.constantCoeff_apply, map_prod, IsUnit.prod_univ_iff]
    intro ψ
    simpa using (hy ψ).neg
  exact Ideal.span_singleton_eq_top.mp
    (Ideal.eq_top_of_isUnit_mem _ hP0_mem (hP0_unit.map (algebraMap O Ψ.charGroupRing)))

/-- **Product criterion for units** (Dasgupta–Kakde, §2.3): for a finite set `Ψ` of characters,
`y ∈ R_Ψ` is a unit in `R_Ψ` if and only if the product `∏_{ψ ∈ Ψ} y(ψ)` is a unit in `O`. -/
theorem isUnit_iff_isUnit_prod [Fintype Ψ] {y : Ψ.charGroupRing} :
    IsUnit y ↔ IsUnit (∏ ψ : Ψ, (y : Ψ → O) ψ) := by
  rw [isUnit_iff, IsUnit.prod_univ_iff]

/-- Over a Noetherian coefficient ring `O`, the character group ring of any finite set `Ψ` of
characters is a finite `O`-module (even when `G` is infinite), as an `O`-submodule of `Ψ → O`. -/
instance [IsNoetherianRing O] : Module.Finite O Ψ.charGroupRing :=
  Module.Finite.of_injective Ψ.charGroupRing.toSubmodule.subtype Subtype.val_injective

end Units

section LocalStructure

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)}

/-- If `p` is a prime that is not a unit in the local ring `O`, then `ResidueField O` has
characteristic `p` (and hence `ExpChar (ResidueField O) p`). -/
theorem charP_residueField_of_not_isUnit {p : ℕ} (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) :
    CharP (IsLocalRing.ResidueField O) p :=
  (CharP.charP_iff_prime_eq_zero hp).mpr <| by
    rwa [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- When `R_Ψ` is a local ring, coordinate evaluation `evalAlgHom hψ : R_Ψ →ₐ[O] O` at any `ψ ∈ Ψ`
is automatically a local homomorphism by surjectivity. -/
theorem isLocalHom_evalAlgHom_of_isLocalRing [IsLocalRing Ψ.charGroupRing]
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalHom (evalAlgHom hψ).toRingHom :=
  (evalAlgHom_surjective hψ).isLocalHom

/-- **Single-character unit criterion** (Dasgupta–Kakde, §2.3): when `R_Ψ` is local and `ψ ∈ Ψ`, an
element `y ∈ R_Ψ` is a unit in `R_Ψ` if and only if `y(ψ)` is a unit in `O`. -/
theorem isUnit_iff_isUnit_eval_of_isLocalRing [IsLocalRing Ψ.charGroupRing]
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) {y : Ψ.charGroupRing} :
    IsUnit y ↔ IsUnit (evalAlgHom hψ y) := by
  have := isLocalHom_evalAlgHom_of_isLocalRing hψ
  exact ⟨fun hy ↦ hy.map _, isUnit_of_map_unit (evalAlgHom hψ).toRingHom y⟩

/-- When `R_Ψ` is local and `ψ ∈ Ψ`, its maximal ideal is the preimage of `maximalIdeal O` under
coordinate evaluation at `ψ`. -/
theorem maximalIdeal_eq_comap [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalRing.maximalIdeal Ψ.charGroupRing =
      (IsLocalRing.maximalIdeal O).comap (evalAlgHom hψ).toRingHom := by
  have := isLocalHom_evalAlgHom_of_isLocalRing hψ
  exact (IsLocalRing.maximalIdeal_comap (evalAlgHom hψ).toRingHom).symm

/-- When `R_Ψ` is local and `ψ ∈ Ψ`, an element `y ∈ R_Ψ` lies in `maximalIdeal R_Ψ` if and only if
its `ψ`-coordinate lies in `maximalIdeal O`. -/
theorem mem_maximalIdeal_iff [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    {y : Ψ.charGroupRing} :
    y ∈ IsLocalRing.maximalIdeal Ψ.charGroupRing ↔
      (y : Ψ → O) ⟨ψ, hψ⟩ ∈ IsLocalRing.maximalIdeal O := by
  rw [maximalIdeal_eq_comap hψ, Ideal.mem_comap]
  rfl

/-- When `R_Ψ` is local, `y ∈ R_Ψ` lies in `maximalIdeal R_Ψ` if and only if every coordinate of
`y` lies in `maximalIdeal O`. -/
theorem mem_maximalIdeal_iff_forall [IsLocalRing Ψ.charGroupRing] {y : Ψ.charGroupRing} :
    y ∈ IsLocalRing.maximalIdeal Ψ.charGroupRing ↔
      ∀ ψ : Ψ, (y : Ψ → O) ψ ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨ψ₀, hψ₀⟩ := nonempty_of_nontrivial (Ψ := Ψ)
  exact ⟨fun hy ψ ↦ (mem_maximalIdeal_iff ψ.2).mp hy,
    fun hy ↦ (mem_maximalIdeal_iff hψ₀).mpr (hy ⟨ψ₀, hψ₀⟩)⟩

/-- When `R_Ψ` is local, the canonical map `ResidueField O →+* ResidueField R_Ψ` is bijective:
`R_Ψ` has no residue field extension over `O`. -/
theorem algebraMap_residueField_bijective [IsLocalRing Ψ.charGroupRing] :
    Function.Bijective
      (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField Ψ.charGroupRing)) := by
  obtain ⟨ψ, hψ⟩ := nonempty_of_nontrivial (Ψ := Ψ)
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  refine ⟨IsLocalRing.residue O (evalAlgHom hψ y), ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff hψ]
  simp

variable (Ψ) in
/-- **Residue field isomorphism**: when `R_Ψ` is local, `ResidueField O` is canonically isomorphic
to `ResidueField R_Ψ` via `algebraMap`. -/
noncomputable def residueFieldEquiv [IsLocalRing Ψ.charGroupRing] :
    IsLocalRing.ResidueField O ≃+* IsLocalRing.ResidueField Ψ.charGroupRing :=
  RingEquiv.ofBijective _ algebraMap_residueField_bijective

/-- `residueFieldEquiv` sends the residue of `a ∈ O` to the residue of `algebraMap O R_Ψ a`. -/
@[simp]
theorem residueFieldEquiv_residue [IsLocalRing Ψ.charGroupRing] (a : O) :
    residueFieldEquiv Ψ (IsLocalRing.residue O a) =
      IsLocalRing.residue Ψ.charGroupRing (algebraMap O Ψ.charGroupRing a) :=
  (rfl)

/-- For any `ψ ∈ Ψ`, the inverse of `residueFieldEquiv` sends the residue of `y ∈ R_Ψ` to the
residue of `y(ψ) ∈ O`. -/
theorem residueFieldEquiv_symm_residue [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    (y : Ψ.charGroupRing) :
    (residueFieldEquiv Ψ).symm (IsLocalRing.residue Ψ.charGroupRing y) =
      IsLocalRing.residue O (evalAlgHom hψ y) := by
  apply (residueFieldEquiv Ψ).injective
  rw [RingEquiv.apply_symm_apply, residueFieldEquiv_residue, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff hψ]
  simp

/-- For any local ring `O` and single character `ψ : G →* Oˣ`, `R_{{ψ}}` is a local ring. -/
instance isLocalRing_singleton (ψ : G →* Oˣ) :
    IsLocalRing ({ψ} : Set (G →* Oˣ)).charGroupRing :=
  (singletonAlgEquiv ψ).symm.toRingEquiv.isLocalRing

/-- **Maximal ideal power containment** (Dasgupta–Kakde, §7.2.9): when `R_Ψ` is local and module-
finite over `O` (e.g. when `G` is finite, or when `O` is Noetherian and `Ψ` is finite), some
positive power `𝔪_{R_Ψ}^N` of its maximal ideal is contained in the extended ideal `𝔪 O · R_Ψ`. -/
theorem exists_maximalIdeal_pow_le_map [IsLocalRing Ψ.charGroupRing]
    [Module.Finite O Ψ.charGroupRing] :
    ∃ N ≥ 1, IsLocalRing.maximalIdeal Ψ.charGroupRing ^ N ≤
      (IsLocalRing.maximalIdeal O).map (algebraMap O Ψ.charGroupRing) := by
  obtain ⟨n, hn⟩ :=
    TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map (R := O) (S := Ψ.charGroupRing)
  refine ⟨max n 1, le_max_right n 1, ?_⟩
  exact (Ideal.pow_le_pow_right (le_max_left n 1)).trans hn

/-- Over a Noetherian ring `O`, any module-finite character group ring `R_Ψ` is a Noetherian ring
(in particular whenever `G` is finite or `Ψ` is finite). -/
instance [IsNoetherianRing O] [Module.Finite O Ψ.charGroupRing] :
    IsNoetherianRing Ψ.charGroupRing :=
  IsNoetherianRing.of_finite O Ψ.charGroupRing

/-- Over a complete Noetherian local ring `O`, any module-finite local character group ring `R_Ψ` is
adically complete with respect to its own maximal ideal (Dasgupta–Kakde, §2.3, §5.1). -/
instance [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [IsLocalRing Ψ.charGroupRing] [Module.Finite O Ψ.charGroupRing] :
    IsAdicComplete (IsLocalRing.maximalIdeal Ψ.charGroupRing) Ψ.charGroupRing :=
  IsAdicComplete.of_finite_of_isLocalRing O Ψ.charGroupRing

section ExpChar

variable (p : ℕ) [ExpChar (IsLocalRing.ResidueField O) p]

/-- Two characters whose values agree up to `p`-th powers on every element of `G` induce identical
evaluations modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_pow_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k) (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) := by
  have hg (g : G) : IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g) := by
    obtain ⟨k, hk⟩ := h g
    have hpow : (IsLocalRing.residue O (ψ₁ g) - IsLocalRing.residue O (ψ₂ g)) ^ p ^ k = 0 := by
      rw [sub_pow_expChar_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← Units.val_pow_eq_pow_val, hk, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a => simp [hg g]

/-- Under `p`-power congruence of characters on `Ψ`, all coordinates of any element `y ∈ R_Ψ` have
the same residue in `ResidueField O`. -/
theorem residue_apply_eq_of_pow_eq
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    (y : Ψ.charGroupRing) (ψ₁ ψ₂ : Ψ) :
    IsLocalRing.residue O ((y : Ψ → O) ψ₁) = IsLocalRing.residue O ((y : Ψ → O) ψ₂) := by
  obtain ⟨x, rfl⟩ := proj_surjective Ψ y
  rw [coe_proj_apply, coe_proj_apply]
  exact residue_charEval_eq_of_pow_eq p (hΨ ψ₁.1 ψ₁.2 ψ₂.1 ψ₂.2) x

/-- **Coordinate evaluation is a local homomorphism**: when `Ψ` is finite and any two characters in
`Ψ` agree up to `p`-th powers on `G`, coordinate evaluation at `ψ ∈ Ψ` reflects units. -/
theorem isLocalHom_evalAlgHom [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalHom (evalAlgHom hψ).toRingHom := by
  refine ⟨fun y hy ↦ isUnit_iff.mpr fun χ ↦ ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, residue_apply_eq_of_pow_eq p hΨ y χ ⟨ψ, hψ⟩,
    IsLocalRing.residue_ne_zero_iff_isUnit]
  exact hy

/-- **Locality criterion for character group rings** (Dasgupta–Kakde, §2.3, §5.1, §7.1): over a
local ring `O` whose residue field has exponential characteristic `p`, the character group ring
`R_Ψ` of any finite nonempty set `Ψ` of characters whose values agree up to `p`-th powers is a local
ring. -/
theorem isLocalRing [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    (hne : Ψ.Nonempty) :
    IsLocalRing Ψ.charGroupRing := by
  obtain ⟨ψ, hψ⟩ := hne
  have := isLocalHom_evalAlgHom p hΨ hψ
  exact (evalAlgHom hψ).toRingHom.domain_isLocalRing

end ExpChar

end LocalStructure

section ComponentLocality

variable {O G : Type*} [CommRing O] [CommGroup G] {P H : Subgroup G}

/-- When `P` and `H` are complementary subgroups of `G` and `P` is a `p`-group, any two characters
of `G` with the same restriction to `H` have values agreeing up to `p`-th powers on all of `G`. -/
theorem pow_eq_of_isPGroup_of_comp_eq {p : ℕ} (hPH : P.IsComplement' H) (hP : IsPGroup p P)
    {ψ₁ ψ₂ : G →* Oˣ} (hH : ψ₁.comp H.subtype = ψ₂.comp H.subtype) (g : G) :
    ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k := by
  obtain ⟨⟨gP, gH⟩, rfl⟩ := hPH.surjective g
  obtain ⟨k, hk⟩ := hP.exists_pow_pow_eq_one gP
  refine ⟨k, ?_⟩
  have h1 : ψ₁ (gP : G) ^ p ^ k = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hk, Subgroup.coe_one, map_one]
  have h2 : ψ₂ (gP : G) ^ p ^ k = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hk, Subgroup.coe_one, map_one]
  have hH' : ψ₁ (gH : G) = ψ₂ (gH : G) := DFunLike.congr_fun hH gH
  dsimp only
  rw [map_mul, map_mul, mul_pow, mul_pow, h1, h2, hH']

/-- For complementary subgroups `P.IsComplement' H`, the `χ`-component character set
`{ψ : G →* Oˣ | ψ.comp H.subtype = χ}` is always nonempty, witnessed by `extendChar hPH 1 χ`. -/
theorem nonempty_componentSet (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.Nonempty :=
  ⟨extendChar hPH 1 χ, extendChar_comp_right hPH 1 χ⟩

/-- For complementary subgroups `P.IsComplement' H` of a finite commutative group `G` and any
nontrivial subgroup `I ≤ P`, when `O` has enough roots of unity of order `exponent G`, there exists
a character of `G` extending `χ` that is nontrivial on `I`. -/
theorem nonempty_componentNormSet [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]
    {I : Subgroup G} (hPH : P.IsComplement' H) (hIP : I ≤ P) (hI : I ≠ ⊥) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}.Nonempty := by
  have : HasEnoughRootsOfUnity O (Monoid.exponent P) :=
    .of_dvd O (Monoid.exponent_dvd_of_monoidHom P.subtype P.subtype_injective)
  obtain ⟨⟨g, hgI⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI
  have ha : (⟨g, hIP hgI⟩ : P) ≠ 1 := by simpa [Subtype.ext_iff] using hg1
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity P O ha
  refine ⟨extendChar hPH φ χ, extendChar_comp_right hPH φ χ, fun hle ↦ hφ ?_⟩
  have hval := DFunLike.congr_fun (extendChar_comp_left hPH φ χ) ⟨g, hIP hgI⟩
  exact hval.symm.trans (hle hgI)

/-- **Locality of character group rings inside a `χ`-component** (Dasgupta–Kakde, §2.3, §5.1,
§7.1): when `(O, 𝔪)` is a local ring of residue exponential characteristic `p`, `P` and `H` are
complementary subgroups of `G` with `P` a `p`-group, and `Ψ` is any finite nonempty subset of
`Ψ_χ = {ψ | ψ.comp H.subtype = χ}`, the character group ring `R_Ψ` is a local ring. In particular,
this applies both to the full component `Ψ_χ` and to norm quotients `Ψ_χ ∩ {ψ | ¬ I ≤ ψ.ker}`. -/
theorem isLocalRing_of_subset_component [IsLocalRing O] (p : ℕ)
    [ExpChar (IsLocalRing.ResidueField O) p] (hPH : P.IsComplement' H) (hP : IsPGroup p P)
    {χ : H →* Oˣ} {Ψ : Set (G →* Oˣ)} [Finite Ψ]
    (hΨ : Ψ ⊆ {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) (hne : Ψ.Nonempty) :
    IsLocalRing Ψ.charGroupRing :=
  isLocalRing p
    (fun _ h₁ _ h₂ ↦ pow_eq_of_isPGroup_of_comp_eq hPH hP ((hΨ h₁).trans (hΨ h₂).symm)) hne

/-- Over a local domain `O` of residue exponential characteristic `p` and a finite group `G = P × H`
with `P` a `p`-group (`IsDomain O` and `Finite G` ensuring finiteness of `G →* Oˣ`), the
`χ`-component character group ring `R_{Ψ_χ}` is a local ring. -/
theorem isLocalRing_component [IsDomain O] [IsLocalRing O] [Finite G] (p : ℕ)
    [ExpChar (IsLocalRing.ResidueField O) p] (hPH : P.IsComplement' H) (hP : IsPGroup p P)
    (χ : H →* Oˣ) :
    IsLocalRing {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing :=
  isLocalRing_of_subset_component p hPH hP Set.Subset.rfl (nonempty_componentSet hPH χ)

-- For any local ring `R` and single character `ψ : M →* Rˣ`, `R_{{ψ}}` is a local ring with
-- residue field canonically isomorphic to `ResidueField R`.
example {R M : Type*} [CommRing R] [IsLocalRing R] [CommGroup M] (ψ : M →* Rˣ) :
    Nonempty (IsLocalRing.ResidueField R ≃+*
      IsLocalRing.ResidueField ({ψ} : Set (M →* Rˣ)).charGroupRing) :=
  ⟨residueFieldEquiv {ψ}⟩

-- Over any local domain `R` whose residue field has characteristic `2`, the character group ring
-- of all characters of the 2-element group `ℤˣ` is a local ring (with `P = ⊤` and `H = ⊥`).
example {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [ExpChar (IsLocalRing.ResidueField R) 2] :
    IsLocalRing (Set.univ : Set (ℤˣ →* Rˣ)).charGroupRing := by
  have hP : IsPGroup 2 (⊤ : Subgroup ℤˣ) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    have hcard : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [Subgroup.card_top, hcard, pow_one]
  have huniv : (Set.univ : Set (ℤˣ →* Rˣ)) ⊆
      {ψ : ℤˣ →* Rˣ | ψ.comp (⊥ : Subgroup ℤˣ).subtype = 1} := fun ψ _ ↦
    MonoidHom.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  exact isLocalRing_of_subset_component 2 Subgroup.isComplement'_top_bot hP huniv ⟨1, trivial⟩

end ComponentLocality

end Set.charGroupRing
