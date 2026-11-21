/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.Algebra.Subalgebra.Pi
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Component
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Finite
public import TauCeti.GroupTheory.PGroup.Quotient
public import TauCeti.RingTheory.AdicCompletion.Finite

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
  a unit in `O`, obtained directly from the general subalgebra unit criteria `Subalgebra.isUnit_iff`
  and `Subalgebra.isUnit_iff_isUnit_prod`.
* **Locality (`Set.charGroupRing.isLocalRing_of_residue_eq`, `Set.charGroupRing.isLocalRing`)**:
  suppose `(O, 𝔪)` is a local ring and `Ψ` is finite, nonempty, and any two characters in `Ψ`
  agree modulo `𝔪` at every `g : G`. Then all members of `Ψ` induce the same homomorphism
  `R_Ψ → ResidueField O` modulo `𝔪`, so coordinate evaluation `evalAlgHom : R_Ψ → O` at any
  `ψ ∈ Ψ` is a local homomorphism (`Set.charGroupRing.isLocalHom_evalAlgHom_of_residue_eq`), and
  `R_Ψ` is a local ring. In particular, when `ResidueField O` has exponential characteristic `p`
  (`[ExpChar (ResidueField O) p]`) and `Ψ` satisfies the `p`-power congruence condition
  `∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁(g)^{p^k} = ψ₂(g)^{p^k}`, `ResidueField O` is reduced
  of exponential characteristic `p`, so characters in `Ψ` agree modulo `𝔪` and `R_Ψ` is a local
  ring!
* **Consequences of locality**: once `[IsLocalRing Ψ.charGroupRing]` holds (with `[Nontrivial O]`,
  and no finiteness or `p`-power hypotheses repeated), surjectivity of `evalAlgHom` makes every
  coordinate evaluation a local homomorphism (`isLocalHom_evalAlgHom_of_isLocalRing`), so `y ∈ R_Ψ`
  is a unit iff `y(ψ) ∈ Oˣ` at any single `ψ ∈ Ψ` via `(isUnit_map_iff (evalAlgHom hψ) y).symm`.
  When `O` is a local ring, this identifies the maximal ideal of `R_Ψ` as the preimage of `𝔪` at
  any single `ψ ∈ Ψ` (`Set.charGroupRing.maximalIdeal_eq_comap`) and identifies the residue field of
  `R_Ψ` with `ResidueField O` (`Set.charGroupRing.residueFieldEquiv`). When in addition `R_Ψ` is
  module-finite over `O` (e.g. when `G` is finite, or when `O` is Noetherian and `Ψ` is finite),
  some positive power of `𝔪_{R_Ψ}` lies inside `𝔪 R_Ψ` by
  `TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map` (Dasgupta–Kakde §7.2.9), and when `O` is a
  complete Noetherian local ring, `R_Ψ` is Noetherian (`Set.charGroupRing.instIsNoetherianRing`)
  and `𝔪_{R_Ψ}`-adically complete.
* **Component specialization (`Set.charGroupRing.isLocalRing_of_subset_component`,
  `Set.charGroupRing.isLocalRing_component`)**: whenever `G ⧸ H` is a `p`-group
  (`IsPGroup p (G ⧸ H)`), any two characters of `G` agreeing on `H` have equal `p^k`-th powers at
  each element of `G` (`IsPGroup.exists_pow_pow_eq_of_comp_eq`), so every finite nonempty subset
  `Ψ ⊆ Ψ_χ` yields a local character group ring `R_Ψ`. In particular, for complementary subgroups
  `P.IsComplement' H` with `P` a `p`-group and `Finite (P →* Oˣ)`, the full component `R_{Ψ_χ}` is
  a local ring.

## Main definitions and results

* `Set.charGroupRing.isUnit_iff` and `Set.charGroupRing.isUnit_iff_isUnit_prod`: unit criteria in
  `R_Ψ` for finite `Ψ`.
* `Set.charGroupRing.isLocalHom_evalAlgHom_of_residue_eq` and
  `Set.charGroupRing.isLocalRing_of_residue_eq`: locality of `R_Ψ` when characters in `Ψ` agree
  modulo the maximal ideal of `O`.
* `Set.charGroupRing.isLocalHom_evalAlgHom` and `Set.charGroupRing.isLocalRing`: locality of `R_Ψ`
  when characters in `Ψ` have equal `p^k`-th powers.
* `Set.charGroupRing.maximalIdeal_eq_comap` and `Set.charGroupRing.residueFieldEquiv`: maximal
  ideal and residue field of a local character group ring.
* `Set.charGroupRing.isLocalRing_of_subset_component` and `Set.charGroupRing.isLocalRing_component`:
  specialization to subsets of a `χ`-component when `G ⧸ H` is a `p`-group.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.3,
  §5.1, §7.1, and §7.2.9.
-/

public section

namespace TauCeti

section ResidueEq

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]

/-- Two characters whose values at every element of `G` agree modulo the maximal ideal of `O`
induce identical evaluations on `O[G]` modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_residue_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a => simp [h g]

end ResidueEq

section ExpChar

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]
variable (p : ℕ) [ExpChar (IsLocalRing.ResidueField O) p]

private theorem residue_eq_of_pow_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k) (g : G) :
    IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g) := by
  obtain ⟨k, hk⟩ := h g
  have hpow : (IsLocalRing.residue O (ψ₁ g) - IsLocalRing.residue O (ψ₂ g)) ^ p ^ k = 0 := by
    rw [sub_pow_expChar_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, hk, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)

/-- Two characters whose values at every element of `G` have equal `p^k`-th powers for some `k`
induce identical evaluations modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_pow_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k) (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) :=
  residue_charEval_eq_of_residue_eq (residue_eq_of_pow_eq p h) x

end ExpChar

end TauCeti

namespace Set.charGroupRing

section Units

variable {O G : Type*} [CommRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)} [Finite Ψ]

/-- **Units of a character group ring**: for a finite set `Ψ` of characters, an element `y ∈ R_Ψ`
is a unit in `R_Ψ` if and only if every coordinate `y(ψ)` is a unit in `O`. -/
theorem isUnit_iff {y : Ψ.charGroupRing} :
    IsUnit y ↔ ∀ ψ : Ψ, IsUnit ((y : Ψ → O) ψ) :=
  Subalgebra.isUnit_iff

omit [Finite Ψ] in
/-- **Product criterion for units** (Dasgupta–Kakde, §2.3): for a finite set `Ψ` of characters,
`y ∈ R_Ψ` is a unit in `R_Ψ` if and only if the product `∏_{ψ ∈ Ψ} y(ψ)` is a unit in `O`. -/
theorem isUnit_iff_isUnit_prod [Fintype Ψ] {y : Ψ.charGroupRing} :
    IsUnit y ↔ IsUnit (∏ ψ : Ψ, (y : Ψ → O) ψ) :=
  Subalgebra.isUnit_iff_isUnit_prod

end Units

section LocalStructure

variable {O G : Type*} [CommRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)}

/-- When `R_Ψ` is a local ring and `R_{Ψ'}` is nontrivial for `Ψ' ⊆ Ψ`, the surjective transition
homomorphism `restrictAlgHom h : R_Ψ →ₐ[O] R_{Ψ'}` is automatically a local homomorphism. -/
instance isLocalHom_restrictAlgHom {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ)
    [IsLocalRing Ψ.charGroupRing] [Nontrivial Ψ'.charGroupRing] :
    IsLocalHom (restrictAlgHom h) :=
  ⟨((restrictAlgHom_surjective h).isLocalHom (f := (restrictAlgHom h).toRingHom)).map_nonunit⟩

/-- When `R_Ψ` is a local ring and `O` is nontrivial, coordinate evaluation
`evalAlgHom hψ : R_Ψ →ₐ[O] O` at any `ψ ∈ Ψ` is automatically a local homomorphism by
surjectivity. In particular, `IsUnit y ↔ IsUnit (evalAlgHom hψ y)` holds by
`(isUnit_map_iff (evalAlgHom hψ) y).symm`. -/
instance isLocalHom_evalAlgHom_of_isLocalRing [Nontrivial O] [IsLocalRing Ψ.charGroupRing]
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalHom (evalAlgHom hψ) :=
  ⟨((evalAlgHom_surjective hψ).isLocalHom (f := (evalAlgHom hψ).toRingHom)).map_nonunit⟩

variable [IsLocalRing O]

/-- When `R_Ψ` is local and `ψ ∈ Ψ`, its maximal ideal is the preimage of `maximalIdeal O` under
coordinate evaluation at `ψ`. -/
theorem maximalIdeal_eq_comap [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalRing.maximalIdeal Ψ.charGroupRing =
      (IsLocalRing.maximalIdeal O).comap (evalAlgHom hψ : Ψ.charGroupRing →+* O) :=
  (IsLocalRing.maximalIdeal_comap (evalAlgHom hψ : Ψ.charGroupRing →+* O)).symm

/-- When `R_Ψ` is local and `ψ ∈ Ψ`, an element `y ∈ R_Ψ` lies in `maximalIdeal R_Ψ` if and only if
its `ψ`-coordinate lies in `maximalIdeal O`. -/
theorem mem_maximalIdeal_iff [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    {y : Ψ.charGroupRing} :
    y ∈ IsLocalRing.maximalIdeal Ψ.charGroupRing ↔
      (y : Ψ → O) ⟨ψ, hψ⟩ ∈ IsLocalRing.maximalIdeal O := by
  simp [maximalIdeal_eq_comap hψ]

/-- When `R_Ψ` is local, `y ∈ R_Ψ` lies in `maximalIdeal R_Ψ` if and only if every coordinate of
`y` lies in `maximalIdeal O`. -/
theorem mem_maximalIdeal_iff_forall [IsLocalRing Ψ.charGroupRing] {y : Ψ.charGroupRing} :
    y ∈ IsLocalRing.maximalIdeal Ψ.charGroupRing ↔
      ∀ ψ : Ψ, (y : Ψ → O) ψ ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨ψ₀, hψ₀⟩ := nonempty_of_nontrivial (Ψ := Ψ)
  exact ⟨fun hy ψ ↦ (mem_maximalIdeal_iff ψ.property).mp hy,
    fun hy ↦ (mem_maximalIdeal_iff hψ₀).mpr (hy ⟨ψ₀, hψ₀⟩)⟩

/-- When `R_Ψ` is local and `ψ ∈ Ψ`, every `y ∈ R_Ψ` has the same residue modulo
`maximalIdeal R_Ψ` as its `ψ`-coordinate `evalAlgHom hψ y` embedded from `O`. -/
theorem residue_algebraMap_evalAlgHom [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    (y : Ψ.charGroupRing) :
    IsLocalRing.residue Ψ.charGroupRing (algebraMap O Ψ.charGroupRing (evalAlgHom hψ y)) =
      IsLocalRing.residue Ψ.charGroupRing y := by
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff hψ]
  simp

/-- When `R_Ψ` is local, the canonical map `ResidueField O →+* ResidueField R_Ψ` is bijective:
`R_Ψ` has no residue field extension over `O`. -/
theorem algebraMap_residueField_bijective [IsLocalRing Ψ.charGroupRing] :
    Function.Bijective
      (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField Ψ.charGroupRing)) := by
  obtain ⟨ψ, hψ⟩ := nonempty_of_nontrivial (Ψ := Ψ)
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  exact ⟨IsLocalRing.residue O (evalAlgHom hψ y),
    (IsLocalRing.ResidueField.algebraMap_residue _).trans (residue_algebraMap_evalAlgHom hψ y)⟩

variable (Ψ) in
/-- **Residue field isomorphism**: when `R_Ψ` is local, `ResidueField O` is canonically isomorphic
to `ResidueField R_Ψ` via `algebraMap`. -/
noncomputable def residueFieldEquiv [IsLocalRing Ψ.charGroupRing] :
    IsLocalRing.ResidueField O ≃+* IsLocalRing.ResidueField Ψ.charGroupRing :=
  RingEquiv.ofBijective _ algebraMap_residueField_bijective

/-- `residueFieldEquiv` acts as `algebraMap (ResidueField O) (ResidueField R_Ψ)`. -/
@[simp]
theorem residueFieldEquiv_apply [IsLocalRing Ψ.charGroupRing] (z : IsLocalRing.ResidueField O) :
    residueFieldEquiv Ψ z =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField Ψ.charGroupRing) z := by
  simp [residueFieldEquiv]

/-- `residueFieldEquiv` sends the residue of `a ∈ O` to the residue of `algebraMap O R_Ψ a`. -/
theorem residueFieldEquiv_residue [IsLocalRing Ψ.charGroupRing] (a : O) :
    residueFieldEquiv Ψ (IsLocalRing.residue O a) =
      IsLocalRing.residue Ψ.charGroupRing (algebraMap O Ψ.charGroupRing a) := by
  simp [residueFieldEquiv_apply]

/-- For any `ψ ∈ Ψ`, the inverse of `residueFieldEquiv` agrees with the residue-field map induced
by coordinate evaluation `evalAlgHom hψ : R_Ψ →+* O`. -/
theorem residueFieldEquiv_symm_apply [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    (w : IsLocalRing.ResidueField Ψ.charGroupRing) :
    (residueFieldEquiv Ψ).symm w =
      IsLocalRing.ResidueField.map (evalAlgHom hψ : Ψ.charGroupRing →+* O) w := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
  rw [IsLocalRing.ResidueField.map_residue]
  apply (residueFieldEquiv Ψ).injective
  rw [RingEquiv.apply_symm_apply, residueFieldEquiv_apply,
    IsLocalRing.ResidueField.algebraMap_residue, AlgHom.coe_toRingHom,
    residue_algebraMap_evalAlgHom hψ y]

/-- For any `ψ ∈ Ψ`, the inverse of `residueFieldEquiv` sends the residue of `y ∈ R_Ψ` to the
residue of `y(ψ) ∈ O`. -/
theorem residueFieldEquiv_symm_residue [IsLocalRing Ψ.charGroupRing] {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ)
    (y : Ψ.charGroupRing) :
    (residueFieldEquiv Ψ).symm (IsLocalRing.residue Ψ.charGroupRing y) =
      IsLocalRing.residue O (evalAlgHom hψ y) := by
  simp [residueFieldEquiv_symm_apply hψ]

/-- For any local ring `O` and single character `ψ : G →* Oˣ`, `R_{{ψ}}` is a local ring. -/
instance isLocalRing_singleton (ψ : G →* Oˣ) :
    IsLocalRing ({ψ} : Set (G →* Oˣ)).charGroupRing :=
  (singletonAlgEquiv ψ).symm.toRingEquiv.isLocalRing

/-- Over a complete Noetherian local ring `O`, any module-finite local character group ring `R_Ψ` is
adically complete with respect to its own maximal ideal (Dasgupta–Kakde, §7.1, §7.2.9). -/
instance [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [IsLocalRing Ψ.charGroupRing] [Module.Finite O Ψ.charGroupRing] :
    IsAdicComplete (IsLocalRing.maximalIdeal Ψ.charGroupRing) Ψ.charGroupRing :=
  IsAdicComplete.of_finite_of_isLocalRing O Ψ.charGroupRing

section ResidueEq

/-- When any two characters in `Ψ` agree modulo the maximal ideal of `O` at every element of `G`,
all coordinates of any element `y ∈ R_Ψ` have the same residue in `ResidueField O`. -/
theorem residue_apply_eq_of_residue_eq
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G,
      IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    (y : Ψ.charGroupRing) (ψ₁ ψ₂ : Ψ) :
    IsLocalRing.residue O ((y : Ψ → O) ψ₁) = IsLocalRing.residue O ((y : Ψ → O) ψ₂) := by
  obtain ⟨x, rfl⟩ := proj_surjective Ψ y
  rw [coe_proj_apply, coe_proj_apply]
  exact TauCeti.residue_charEval_eq_of_residue_eq (hΨ ψ₁.val ψ₁.property ψ₂.val ψ₂.property) x

/-- **Coordinate evaluation is a local homomorphism**: when `Ψ` is finite and any two characters in
`Ψ` agree modulo the maximal ideal of `O` at each element of `G`, coordinate evaluation at `ψ ∈ Ψ`
reflects units. -/
theorem isLocalHom_evalAlgHom_of_residue_eq [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G,
      IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalHom (evalAlgHom hψ) := by
  refine ⟨fun y hy ↦ isUnit_iff.mpr fun χ ↦ ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, residue_apply_eq_of_residue_eq hΨ y χ ⟨ψ, hψ⟩,
    IsLocalRing.residue_ne_zero_iff_isUnit, ← evalAlgHom_apply hψ]
  exact hy

/-- **Locality criterion for character group rings via residue equality**: over a local ring `O`,
the character group ring `R_Ψ` of any finite nonempty set `Ψ` of characters whose values at each
element of `G` agree modulo the maximal ideal of `O` is a local ring. -/
theorem isLocalRing_of_residue_eq [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G,
      IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    (hne : Ψ.Nonempty) :
    IsLocalRing Ψ.charGroupRing := by
  obtain ⟨ψ, hψ⟩ := hne
  have := isLocalHom_evalAlgHom_of_residue_eq hΨ hψ
  exact (evalAlgHom hψ : Ψ.charGroupRing →+* O).domain_isLocalRing

end ResidueEq

section ExpChar

variable (p : ℕ) [ExpChar (IsLocalRing.ResidueField O) p]

/-- When any two characters in `Ψ` have equal `p^k`-th powers at every element of `G` for some `k`,
all coordinates of any element `y ∈ R_Ψ` have the same residue in `ResidueField O`. -/
theorem residue_apply_eq_of_pow_eq
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    (y : Ψ.charGroupRing) (ψ₁ ψ₂ : Ψ) :
    IsLocalRing.residue O ((y : Ψ → O) ψ₁) = IsLocalRing.residue O ((y : Ψ → O) ψ₂) :=
  residue_apply_eq_of_residue_eq
    (fun _ h₁ _ h₂ ↦ TauCeti.residue_eq_of_pow_eq p (hΨ _ h₁ _ h₂)) y ψ₁ ψ₂

/-- **Coordinate evaluation is a local homomorphism**: when `Ψ` is finite and any two characters in
`Ψ` have equal `p^k`-th powers at each element of `G` for some `k`, coordinate evaluation at
`ψ ∈ Ψ` reflects units. -/
theorem isLocalHom_evalAlgHom [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    {ψ : G →* Oˣ} (hψ : ψ ∈ Ψ) :
    IsLocalHom (evalAlgHom hψ) :=
  isLocalHom_evalAlgHom_of_residue_eq
    (fun _ h₁ _ h₂ ↦ TauCeti.residue_eq_of_pow_eq p (hΨ _ h₁ _ h₂)) hψ

/-- **Locality criterion for character group rings** (Dasgupta–Kakde, §2.3, §5.1, §7.1): over a
local ring `O` whose residue field has exponential characteristic `p`, the character group ring
`R_Ψ` of any finite nonempty set `Ψ` of characters whose values at each element of `G` have equal
`p^k`-th powers for some `k` is a local ring. -/
theorem isLocalRing [Finite Ψ]
    (hΨ : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k)
    (hne : Ψ.Nonempty) :
    IsLocalRing Ψ.charGroupRing :=
  isLocalRing_of_residue_eq
    (fun _ h₁ _ h₂ ↦ TauCeti.residue_eq_of_pow_eq p (hΨ _ h₁ _ h₂)) hne

end ExpChar

end LocalStructure

section ComponentLocality

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]

/-- **Locality of character group rings inside a `χ`-component** (Dasgupta–Kakde, §2.3, §5.1,
§7.1): when `(O, 𝔪)` is a local ring of residue exponential characteristic `p`, `H ≤ G` is a
subgroup such that `G ⧸ H` is a `p`-group (`IsPGroup p (G ⧸ H)`), and `Ψ` is any finite nonempty
subset of `Ψ_χ = {ψ | ψ.comp H.subtype = χ}`, the character group ring `R_Ψ` is a local ring. In
particular, this applies both to the full component `Ψ_χ` and to norm quotients
`Ψ_χ ∩ {ψ | ¬ I ≤ ψ.ker}`. -/
theorem isLocalRing_of_subset_component (p : ℕ) [ExpChar (IsLocalRing.ResidueField O) p]
    {H : Subgroup G} (hGH : IsPGroup p (G ⧸ H)) {χ : H →* Oˣ} {Ψ : Set (G →* Oˣ)} [Finite Ψ]
    (hΨ : Ψ ⊆ {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) (hne : Ψ.Nonempty) :
    IsLocalRing Ψ.charGroupRing :=
  isLocalRing p
    (fun _ h₁ _ h₂ ↦ hGH.exists_pow_pow_eq_of_comp_eq ((hΨ h₁).trans (hΨ h₂).symm)) hne

/-- Over a local ring `O` of residue exponential characteristic `p` and complementary subgroups
`P.IsComplement' H` with `P` a `p`-group and `Finite (P →* Oˣ)` (ensuring finiteness of
`{ψ : G →* Oˣ | ψ.comp H.subtype = χ}`), the `χ`-component character group ring `R_{Ψ_χ}` is a
local ring. -/
theorem isLocalRing_component {P H : Subgroup G} [Finite (P →* Oˣ)] (p : ℕ)
    [ExpChar (IsLocalRing.ResidueField O) p] (hPH : P.IsComplement' H) (hP : IsPGroup p P)
    (χ : H →* Oˣ) :
    IsLocalRing {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing := by
  have : Finite {ψ : G →* Oˣ | ψ.comp H.subtype = χ} :=
    Finite.of_surjective
      (fun φ : P →* Oˣ ↦ (⟨hPH.extendChar φ χ, hPH.extendChar_comp_right φ χ⟩ :
        {ψ : G →* Oˣ | ψ.comp H.subtype = χ}))
      fun ⟨ψ, hψ⟩ ↦ ⟨ψ.comp P.subtype, Subtype.ext <| by
        dsimp only
        rw [← Set.mem_ofPred_eq.mp hψ, hPH.extendChar_comp_self]⟩
  exact isLocalRing_of_subset_component p (hP.of_equiv hPH.QuotientMulEquiv.symm)
    Set.Subset.rfl (nonempty_componentSet hPH χ)

-- For any local ring `R` and single character `ψ : M →* Rˣ`, `R_{{ψ}}` is a local ring with
-- residue field canonically isomorphic to `ResidueField R`.
example {R M : Type*} [CommRing R] [IsLocalRing R] [CommGroup M] (ψ : M →* Rˣ) :
    Nonempty (IsLocalRing.ResidueField R ≃+*
      IsLocalRing.ResidueField ({ψ} : Set (M →* Rˣ)).charGroupRing) :=
  ⟨residueFieldEquiv {ψ}⟩

-- Over any local domain `R` whose residue field has characteristic `2`, the character group ring
-- of all characters of the 2-element group `ℤˣ` is a local ring (with `H = ⊥`).
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
  exact isLocalRing_of_subset_component 2
    (hP.of_equiv Subgroup.isComplement'_top_bot.QuotientMulEquiv.symm) huniv ⟨1, trivial⟩

end ComponentLocality

end Set.charGroupRing
