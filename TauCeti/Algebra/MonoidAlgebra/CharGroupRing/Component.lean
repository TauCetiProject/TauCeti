/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Norm
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Character components of group rings as character group rings

Let `O` be a commutative ring, `G` a commutative group, `H` a subgroup of `G`, and `χ : H →* Oˣ` a
character of `H`. Let `Ψ_χ = {ψ : G →* Oˣ | ψ.comp H.subtype = χ}` be the set of characters of `G`
extending `χ`. Following Dasgupta and Kakde (§2.2–§2.3), this file relates the character group ring
`R_{Ψ_χ}` to character idempotents, norm quotients, and complementary subgroup rings:

* **Idempotent description and product decomposition** (when `H` is finite and `#H` is a unit in
  `O`): the embedded character idempotent `e_χ = (#H)⁻¹ ∑_{h ∈ H} χ(h)⁻¹ h ∈ O[G]` evaluates to `1`
  on `Ψ_χ` and to `0` on every other character of `G`. When `G` is finite and `O` is a domain with
  enough roots of unity, `ker α_{Ψ_χ} = (1 - e_χ)` and the projections assemble into an `O`-algebra
  isomorphism `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` (`Set.charGroupRing.piComponentAlgEquiv`). Neither a
  complement to `H` in `G` nor any hypothesis on the quotient `G / H` is required here.
* **Norm quotients of a component** (Dasgupta–Kakde, Corollary 2.3): for any second finite subgroup
  `I ≤ G`, when `#H` is a unit in `O`, the quotient of `R_{Ψ_χ}` by the image of the norm element
  `N_I = ∑_{σ ∈ I} σ` is canonically isomorphic to `R_{Ψ_χ ∩ Ψ_I}`, where
  `Ψ_I = {ψ | ¬ I ≤ ψ.ker}` (`Set.charGroupRing.componentQuotientSpanNormAlgEquiv`).
* **Complementary subgroup isomorphism** (`R_{Ψ_χ} ≃ₐ[O] O[P]`): when `P` and `H` are complementary
  subgroups of `G` (`P.IsComplement' H`, e.g. `G = G_p × G'`), sending `p * h ↦ χ(h) p` defines a
  surjective `O`-algebra homomorphism `componentProj : O[G] →ₐ[O] O[P]`. Over any commutative ring
  in which `#H` is a unit, its kernel is `(1 - e_χ)` (`Set.charGroupRing.ker_componentProj`). Over
  a domain with enough roots of unity for finite `G`, `R_{Ψ_χ} ≃ₐ[O] O[P]` holds *without* assuming
  that `#H` is a unit in `O` (`Set.charGroupRing.componentEquiv`), because characters of `P` pair
  bijectively with members of `Ψ_χ` via `Set.charGroupRing.extendChar`.

## Main definitions

* `Set.charGroupRing.piComponentAlgEquiv`: the decomposition `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` when `#H` is
  a unit in `O`.
* `Set.charGroupRing.componentQuotientSpanNormAlgEquiv`: the norm-quotient isomorphism
  `R_{Ψ_χ} / (α_{Ψ_χ}(N_I)) ≃ₐ[O] R_{Ψ_χ ∩ Ψ_I}` (Dasgupta–Kakde, Corollary 2.3).
* `Set.charGroupRing.extendChar`: extension of `(φ : P →* Oˣ)` and `(χ : H →* Oˣ)` across
  complementary subgroups `P.IsComplement' H` to a character `G →* Oˣ`.
* `Set.charGroupRing.componentProj`: the `χ`-twisted projection `O[G] →ₐ[O] O[P]` sending
  `p * h ↦ χ(h) p`.
* `Set.charGroupRing.componentEquiv`: the `O`-algebra isomorphism `R_{Ψ_χ} ≃ₐ[O] O[P]`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), §2.2
  (Corollary 2.3) and §2.3, pp. 16–18.
-/

public section

namespace MonoidHom

section CommSemiring

variable {O H G : Type*} [CommSemiring O] [CommGroup H] [CommGroup G]

/-- Evaluating at `ψ : G →* Oˣ` after mapping the group along `f : H →* G` agrees with evaluating
at the restricted character `ψ.comp f`. -/
@[simp]
theorem charEval_mapDomain (ψ : G →* Oˣ) (f : H →* G) (y : MonoidAlgebra O H) :
    ψ.charEval (MonoidAlgebra.mapDomain f y) = (ψ.comp f).charEval y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [MonoidAlgebra.mapDomain_add, map_add, map_add, hx, hy]
  | single h a => simp

/-- Evaluating at `ψ : G →* Oˣ` after pushing `O[H]` forward along `f : H →* G` agrees with
evaluating at the restricted character `ψ.comp f`. -/
theorem charEval_mapDomainAlgHom (ψ : G →* Oˣ) (f : H →* G) (y : MonoidAlgebra O H) :
    ψ.charEval (MonoidAlgebra.mapDomainAlgHom O O f y) = (ψ.comp f).charEval y := by
  simp

end CommSemiring

section CommRing

variable {O H G : Type*} [CommRing O] [CommGroup H] [Fintype H] [CommGroup G]

/-- When `#H` is a unit in `O`, a character `χ` evaluates to `1` on its own character idempotent
`e_χ`. No domain hypothesis on `O` is required. -/
theorem charEval_charIdempotent_self (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    χ.charEval (TauCeti.charIdempotent χ) = 1 := by
  rw [TauCeti.charIdempotent_eq_sum, map_smul, map_sum]
  simp only [map_smul, MonoidAlgebra.of_apply, TauCeti.DiagonalizableGroup.point_single_one,
    smul_eq_mul, Units.inv_mul, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_one, Ring.inverse_mul_cancel _ hH]

/-- Over a domain, a character `ψ` vanishes on the character idempotent `e_χ` of any distinct
character `χ ≠ ψ`. No unit hypothesis on `#H` is required. -/
theorem charEval_charIdempotent_of_ne [IsDomain O] {χ ψ : H →* Oˣ} (h : χ ≠ ψ) :
    ψ.charEval (TauCeti.charIdempotent χ) = 0 := by
  have hsum : ∑ a : H, (((χ a)⁻¹ : Oˣ) : O) * (ψ a : O) = 0 := by
    have hne : (Units.coeHom O).comp (χ⁻¹ * ψ) ≠ 1 := fun h0 ↦ h <| inv_mul_eq_one.mp <|
      MonoidHom.ext fun a ↦ Units.ext <| by simpa using DFunLike.congr_fun h0 a
    simpa using sum_hom_units_eq_zero _ hne
  rw [TauCeti.charIdempotent_eq_sum, map_smul, map_sum]
  simp [hsum]

/-- Over a domain in which `#H` is a unit, `e_χ` evaluates to the Kronecker delta at characters of
`H`. -/
theorem charEval_charIdempotent [IsDomain O] [DecidableEq (H →* Oˣ)]
    (hH : IsUnit (Nat.card H : O)) (χ ψ : H →* Oˣ) :
    ψ.charEval (TauCeti.charIdempotent χ) = if χ = ψ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact charEval_charIdempotent_self hH χ
  · exact charEval_charIdempotent_of_ne h

omit [Fintype H] in
/-- For a finite subgroup `H ≤ G` whose order is a unit in the domain `O`, the embedded character
idempotent of `χ : H →* Oˣ` in `O[G]` evaluates to `1` at extensions of `χ` and to `0` at all
other characters of `G`. -/
theorem charEval_mapDomainAlgHom_charIdempotent [IsDomain O] (H : Subgroup G) [Fintype H]
    [DecidableEq (H →* Oˣ)] (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) (ψ : G →* Oˣ) :
    ψ.charEval (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) =
      if ψ.comp H.subtype = χ then 1 else 0 := by
  rw [charEval_mapDomainAlgHom, charEval_charIdempotent hH]
  simp_rw [eq_comm]

end CommRing

end MonoidHom

namespace Set.charGroupRing

section Restrict

variable {O G : Type*} [CommSemiring O] [CommGroup G]

/-- For `Ψ' ⊆ Ψ`, restricting functions from `Ψ` to `Ψ'` defines the canonical surjective
`O`-algebra transition homomorphism `R_Ψ →ₐ[O] R_{Ψ'}` through which `α_{Ψ'}` factors. -/
def restrictAlgHom {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) :
    Ψ.charGroupRing →ₐ[O] Ψ'.charGroupRing where
  toFun y := ⟨fun ψ ↦ (y : Ψ → O) ⟨ψ.1, h ψ.2⟩, by
    obtain ⟨x, hx⟩ := mem_iff.mp y.2
    exact mem_iff.mpr ⟨x, fun ψ ↦ hx ⟨ψ.1, h ψ.2⟩⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Coordinatewise formula for `restrictAlgHom`. -/
@[simp]
theorem coe_restrictAlgHom_apply {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ)
    (y : Ψ.charGroupRing) (ψ : Ψ') :
    (restrictAlgHom h y : Ψ' → O) ψ = (y : Ψ → O) ⟨ψ.1, h ψ.2⟩ :=
  (rfl)

/-- `restrictAlgHom` commutes with the canonical projections `α_Ψ` and `α_{Ψ'}`. -/
@[simp]
theorem restrictAlgHom_proj {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) (x : MonoidAlgebra O G) :
    restrictAlgHom h (proj Ψ x) = proj Ψ' x := by
  ext ψ
  simp

/-- `restrictAlgHom` is surjective whenever `Ψ' ⊆ Ψ`. -/
theorem restrictAlgHom_surjective {Ψ' Ψ : Set (G →* Oˣ)} (h : Ψ' ⊆ Ψ) :
    Function.Surjective (restrictAlgHom h) := fun y ↦ by
  obtain ⟨x, rfl⟩ := proj_surjective Ψ' y
  exact ⟨proj Ψ x, restrictAlgHom_proj h x⟩

end Restrict

section IdempotentAndNorm

variable {O G : Type*} [CommRing O] [CommGroup G]

/-- When `#H` is a unit in `O`, `1 - e_χ` vanishes on every character of `G` extending `χ`, where
`e_χ` is the character idempotent of `χ` pushed forward from `O[H]` to `O[G]`. -/
theorem one_sub_charIdempotent_mem_ker_proj (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) ∈
      RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) := by
  rw [RingHom.mem_ker, proj_eq_zero_iff]
  intro ψ hψ
  rw [map_sub, map_one, ψ.charEval_mapDomainAlgHom, hψ, χ.charEval_charIdempotent_self hH,
    sub_self]

variable [IsDomain O] [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- For a finite commutative group `G`, a subgroup `H` with `#H` a unit in the domain `O`, and a
character `χ : H →* Oˣ`, the kernel of `α_{Ψ_χ} : O[G] → R_{Ψ_χ}` is the principal ideal `(1 - e_χ)`
generated by the complementary idempotent of `χ`. -/
theorem ker_proj_eq_span_one_sub_charIdempotent (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) =
      Ideal.span
        {(1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ))} := by
  let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  refine le_antisymm (fun x hx ↦ ?_)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (one_sub_charIdempotent_mem_ker_proj H hH χ)))
  rw [RingHom.mem_ker, proj_eq_zero_iff] at hx
  have hex : e * x = 0 := TauCeti.eq_of_forall_charEval_eq fun ψ ↦ by
    rw [map_mul, map_zero]
    by_cases hψ : ψ.comp H.subtype = χ
    · rw [hx ψ hψ, mul_zero]
    · rw [ψ.charEval_mapDomainAlgHom, MonoidHom.charEval_charIdempotent_of_ne (Ne.symm hψ),
        zero_mul]
  exact Ideal.mem_span_singleton.mpr ⟨x, by rw [sub_mul, one_mul, hex, sub_zero]⟩

/-- **Decomposition of a group ring into character components**: when `H ≤ G` has order invertible
in `O`, the product of the canonical projections `α_{Ψ_χ} : O[G] → R_{Ψ_χ}` over all `χ : H →* Oˣ`
is an `O`-algebra isomorphism `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}`. -/
noncomputable def piComponentAlgEquiv (H : Subgroup G)
    (hH : IsUnit (Nat.card H : O)) :
    MonoidAlgebra O G ≃ₐ[O] ∀ χ : H →* Oˣ, {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing := by
  classical
  let := Fintype.ofFinite H
  let := Fintype.ofFinite (H →* Oˣ)
  refine AlgEquiv.ofBijective
    (AlgHom.pi fun χ : H →* Oˣ ↦ proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) ⟨?_, ?_⟩
  · intro x y hxy
    refine TauCeti.eq_of_forall_charEval_eq fun ψ ↦ ?_
    simpa using congrArg
      (fun g : (∀ χ : H →* Oˣ, {ψ' : G →* Oˣ | ψ'.comp H.subtype = χ}.charGroupRing) ↦
        (g (ψ.comp H.subtype) :
          {ψ' : G →* Oˣ | ψ'.comp H.subtype = ψ.comp H.subtype} → O) ⟨ψ, rfl⟩)
      hxy
  · intro f
    choose x hx using fun χ : H →* Oˣ ↦ proj_surjective _ (f χ)
    refine ⟨∑ χ : H →* Oˣ,
      MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x χ, ?_⟩
    ext χ₀ ⟨ψ, hψ⟩
    have hterm (χ : H →* Oˣ) :
        ψ.charEval
          (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x χ) =
          if χ₀ = χ then ψ.charEval (x χ) else 0 := by
      have hψ' : ψ.comp H.subtype = χ₀ := hψ
      rw [map_mul, MonoidHom.charEval_mapDomainAlgHom_charIdempotent H hH, hψ']
      split_ifs <;> simp
    have hfx : ψ.charEval (x χ₀) =
        (f χ₀ : {ψ' : G →* Oˣ | ψ'.comp H.subtype = χ₀} → O) ⟨ψ, hψ⟩ := by
      rw [← hx χ₀, coe_proj_apply]
    rw [AlgHom.pi_apply, coe_proj_apply, map_sum]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hfx]

/-- The `χ`-coordinate of `piComponentAlgEquiv` is the projection `α_{Ψ_χ}`. -/
@[simp]
theorem piComponentAlgEquiv_apply (H : Subgroup G) (hH : IsUnit (Nat.card H : O))
    (x : MonoidAlgebra O G) (χ : H →* Oˣ) :
    piComponentAlgEquiv H hH x χ = proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x :=
  (rfl)

/-- Projecting `(piComponentAlgEquiv H hH).symm f` onto the `χ`-component recovers `f χ`. -/
@[simp]
theorem proj_piComponentAlgEquiv_symm (H : Subgroup G) (hH : IsUnit (Nat.card H : O))
    (f : ∀ χ : H →* Oˣ, {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) (χ : H →* Oˣ) :
    proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} ((piComponentAlgEquiv H hH).symm f) = f χ :=
  congr_fun ((piComponentAlgEquiv H hH).apply_symm_apply f) χ

/-- **Kernel of a norm-and-component character group ring** (Dasgupta–Kakde, Corollary 2.3): when
`#H` is a unit in `O`, the kernel of `α_Ψ` for `Ψ = {ψ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}` is
generated by `1 - e_χ` and the subgroup norm `N_I = ∑_{σ ∈ I} σ`. -/
theorem ker_proj_component_norm (H I : Subgroup G) [Fintype H] [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}) =
      Ideal.span {(1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)),
        TauCeti.subgroupCharSum (1 : G →* O) I} := by
  let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  let N := TauCeti.subgroupCharSum (1 : G →* O) I
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.mpr ?_)
  · rw [RingHom.mem_ker, proj_eq_zero_iff] at hx
    have hex : e * x ∈ Ideal.span {N} := by
      rw [← ker_proj_eq_span_norm I, RingHom.mem_ker, proj_eq_zero_iff]
      intro ψ hI
      rw [map_mul]
      by_cases hψ : ψ.comp H.subtype = χ
      · rw [hx ψ ⟨hψ, hI⟩, mul_zero]
      · rw [ψ.charEval_mapDomainAlgHom, MonoidHom.charEval_charIdempotent_of_ne (Ne.symm hψ),
          zero_mul]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hex
    refine Ideal.mem_span_pair.mpr ⟨x, y, ?_⟩
    rw [mul_sub, mul_one, mul_comm x, hy, mul_comm y N, sub_add_cancel]
  · rintro z (rfl | hN)
    · rw [SetLike.mem_coe, RingHom.mem_ker, proj_eq_zero_iff]
      intro ψ hψ
      exact proj_eq_zero_iff.mp (one_sub_charIdempotent_mem_ker_proj H hH χ) ψ hψ.1
    · rw [Set.mem_singleton_iff.mp hN, SetLike.mem_coe, RingHom.mem_ker, proj_eq_zero_iff]
      intro ψ hψ
      exact ψ.charEval_subgroupCharSum_one_eq_zero I hψ.2

omit [IsDomain O] [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)] in
/-- Inclusion of `Ψ_χ ∩ Ψ_I` into `Ψ_χ`. -/
theorem componentNorm_subset (H I : Subgroup G) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker} ⊆
      {ψ : G →* Oˣ | ψ.comp H.subtype = χ} :=
  fun _ h ↦ h.1

/-- When `#H` is a unit in `O`, the kernel of the restriction `R_{Ψ_χ} → R_{Ψ_χ ∩ Ψ_I}` is the
principal ideal generated by `α_{Ψ_χ}(N_I)`. -/
theorem ker_restrictAlgHom_component_norm (H I : Subgroup G) [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (restrictAlgHom (componentNorm_subset H I χ)) =
      Ideal.span {(proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (TauCeti.subgroupCharSum (1 : G →* O) I))} := by
  let := Fintype.ofFinite H
  ext xbar
  obtain ⟨x, rfl⟩ := proj_surjective {ψ : G →* Oˣ | ψ.comp H.subtype = χ} xbar
  rw [RingHom.mem_ker, restrictAlgHom_proj, ← RingHom.mem_ker, ker_proj_component_norm H I hH χ,
    Ideal.mem_span_pair, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨proj _ b, ?_⟩
    have ha : proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) = 0 :=
      one_sub_charIdempotent_mem_ker_proj H hH χ
    rw [map_add, map_mul, map_mul, ha, mul_zero, zero_add, mul_comm]
  · rintro ⟨ybar, hy⟩
    obtain ⟨y, rfl⟩ := proj_surjective {ψ : G →* Oˣ | ψ.comp H.subtype = χ} ybar
    have hsub : x - TauCeti.subgroupCharSum (1 : G →* O) I * y ∈
        RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) := by
      rw [RingHom.mem_ker, map_sub, map_mul, hy, sub_self]
    rw [ker_proj_eq_span_one_sub_charIdempotent H hH χ, Ideal.mem_span_singleton] at hsub
    obtain ⟨z, hz⟩ := hsub
    exact ⟨z, y, by rw [mul_comm z, ← hz, mul_comm y, sub_add_cancel]⟩

/-- **Norm quotients of a character component are character group rings** (Dasgupta–Kakde,
Corollary 2.3): when `#H` is a unit in `O`, dividing the `χ`-component `R_{Ψ_χ}` by the image of
the norm element `N_I = ∑_{σ ∈ I} σ` yields the character group ring `R_{Ψ_χ ∩ Ψ_I}` of characters
extending `χ` that are nontrivial on `I`. -/
noncomputable def componentQuotientSpanNormAlgEquiv (H I : Subgroup G) [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    ({ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing ⧸
      Ideal.span {(proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (TauCeti.subgroupCharSum (1 : G →* O) I))}) ≃ₐ[O]
      {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}.charGroupRing :=
  (Ideal.quotientEquivAlgOfEq O (ker_restrictAlgHom_component_norm H I hH χ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (restrictAlgHom_surjective (componentNorm_subset H I χ)))

/-- `componentQuotientSpanNormAlgEquiv` acts on residue classes in `R_{Ψ_χ}` by `restrictAlgHom`. -/
@[simp]
theorem componentQuotientSpanNormAlgEquiv_mk (H I : Subgroup G) [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ)
    (y : {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) :
    componentQuotientSpanNormAlgEquiv H I hH χ
      (Ideal.Quotient.mk
        (Ideal.span {(proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
          (TauCeti.subgroupCharSum (1 : G →* O) I))})
        y) =
      restrictAlgHom (componentNorm_subset H I χ) y :=
  (rfl)

/-- The inverse of `componentQuotientSpanNormAlgEquiv` sends `α_{Ψ_χ ∩ Ψ_I}(x)` to the residue
class of `α_{Ψ_χ}(x)` modulo `(N_I)`. -/
@[simp]
theorem componentQuotientSpanNormAlgEquiv_symm_proj (H I : Subgroup G) [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    (componentQuotientSpanNormAlgEquiv H I hH χ).symm
      (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker} x) =
      Ideal.Quotient.mk
        (Ideal.span {(proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
          (TauCeti.subgroupCharSum (1 : G →* O) I))})
        (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x) := by
  apply (componentQuotientSpanNormAlgEquiv H I hH χ).injective
  rw [AlgEquiv.apply_symm_apply, componentQuotientSpanNormAlgEquiv_mk, restrictAlgHom_proj]

end IdempotentAndNorm

section Complement

variable {O G : Type*} [CommRing O] [CommGroup G] {P H : Subgroup G}

/-- Given complementary subgroups `P` and `H` of a commutative group `G`, combine characters
`φ : P →* Oˣ` and `χ : H →* Oˣ` into the unique character `G →* Oˣ` sending `p * h ↦ φ(p) χ(h)`. -/
noncomputable def extendChar (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) : G →* Oˣ :=
  ((φ.comp (MonoidHom.fst P H)) * (χ.comp (MonoidHom.snd P H))).comp
    (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm.toMonoidHom

/-- `extendChar hPH φ χ` sends `(p : G) * (h : G)` to `φ p * χ h`. -/
@[simp]
theorem extendChar_mul (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) (p : P) (h : H) :
    extendChar hPH φ χ ((p : G) * (h : G)) = φ p * χ h := by
  have he : (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm ((p : G) * (h : G)) =
      (p, h) :=
    (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm_apply_apply (p, h)
  simp [extendChar, he]

/-- Restricting `extendChar hPH φ χ` to `P` recovers `φ`. -/
@[simp]
theorem extendChar_comp_left (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) :
    (extendChar hPH φ χ).comp P.subtype = φ :=
  MonoidHom.ext fun p ↦ by simpa using extendChar_mul hPH φ χ p 1

/-- Restricting `extendChar hPH φ χ` to `H` recovers `χ`. -/
@[simp]
theorem extendChar_comp_right (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) :
    (extendChar hPH φ χ).comp H.subtype = χ :=
  MonoidHom.ext fun h ↦ by simpa using extendChar_mul hPH φ χ 1 h

/-- Every character of `G` is `extendChar` of its restrictions to `P` and `H`. -/
@[simp]
theorem extendChar_comp_self (hPH : P.IsComplement' H) (ψ : G →* Oˣ) :
    extendChar hPH (ψ.comp P.subtype) (ψ.comp H.subtype) = ψ :=
  MonoidHom.ext fun g ↦ by
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.surjective g
    dsimp only
    simpa [map_mul] using extendChar_mul hPH (ψ.comp P.subtype) (ψ.comp H.subtype) p h

/-- **The `χ`-component projection `O[G] →ₐ[O] O[P]`** across complementary subgroups
`P.IsComplement' H`: the `O`-algebra homomorphism sending `(p : G) * (h : G)` to `χ(h) • p` for
`p ∈ P` and `h ∈ H` (Dasgupta–Kakde, §2.3). -/
noncomputable def componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    MonoidAlgebra O G →ₐ[O] MonoidAlgebra O P :=
  let f : P × H →* MonoidAlgebra O P :=
    { toFun := fun x ↦ MonoidAlgebra.single x.1 (χ x.2 : O)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := fun x y ↦ by simp [MonoidAlgebra.single_mul_single] }
  MonoidAlgebra.lift O (MonoidAlgebra O P) G
    (f.comp (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm.toMonoidHom)

/-- `componentProj` sends `single (p * h) a` to `single p (a * χ(h))` for `p ∈ P` and `h ∈ H`. -/
@[simp]
theorem componentProj_single_mul (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (p : P) (h : H) (a : O) :
    componentProj hPH χ (MonoidAlgebra.single ((p : G) * (h : G)) a) =
      MonoidAlgebra.single p (a * (χ h : O)) := by
  have he : (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm ((p : G) * (h : G)) =
      (p, h) :=
    (MulEquiv.ofBijective (P.subtype.coprod H.subtype) hPH).symm_apply_apply (p, h)
  simp [componentProj, he, MonoidAlgebra.smul_single]

/-- Applying `componentProj` to an element pushed forward from `O[P]` recovers it. -/
theorem componentProj_mapDomainAlgHom_left (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O P.subtype y) = y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single p a => simpa using componentProj_single_mul hPH χ p 1 a

/-- `componentProj` is a left inverse to the canonical inclusion `O[P] →ₐ[O] O[G]`. -/
@[simp]
theorem componentProj_comp_mapDomainAlgHom_left (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    (componentProj hPH χ).comp (MonoidAlgebra.mapDomainAlgHom O O P.subtype) =
      AlgHom.id O (MonoidAlgebra O P) :=
  AlgHom.ext (componentProj_mapDomainAlgHom_left hPH χ)

/-- `componentProj` is surjective, with right inverse `mapDomainAlgHom O O P.subtype`. -/
theorem componentProj_surjective (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    Function.Surjective (componentProj hPH χ) :=
  Function.RightInverse.surjective (componentProj_mapDomainAlgHom_left hPH χ)

/-- On `O[H] ⊆ O[G]`, `componentProj hPH χ` acts as scalar evaluation `χ.charEval` followed by
`algebraMap O O[P]`. -/
theorem componentProj_mapDomainAlgHom_right (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O H) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O H.subtype y) =
      algebraMap O (MonoidAlgebra O P) (χ.charEval y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | single h a =>
    simpa [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single] using
      componentProj_single_mul hPH χ 1 h a

/-- Evaluating `componentProj hPH χ x` at a character `φ : P →* Oˣ` agrees with evaluating `x` at
the extended character `extendChar hPH φ χ : G →* Oˣ`. -/
@[simp]
theorem charEval_componentProj (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ)
    (x : MonoidAlgebra O G) :
    φ.charEval (componentProj hPH χ x) = (extendChar hPH φ χ).charEval x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a =>
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.surjective g
    dsimp only
    simp [mul_assoc, mul_comm (χ h : O)]

/-- Multiplying any `x ∈ O[G]` by the embedded character idempotent `e_χ` agrees with multiplying
the `P`-component lift `componentProj hPH χ x` by `e_χ`. -/
theorem charIdempotent_mul_eq_mul_mapDomain_componentProj [Fintype H] (hPH : P.IsComplement' H)
    (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x =
      MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) *
        MonoidAlgebra.mapDomainAlgHom O O P.subtype (componentProj hPH χ x) := by
  have he_mul (h : H) :
      MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) *
        MonoidAlgebra.single (h : G) (1 : O) =
      (χ h : O) • MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) := by
    have hh : MonoidAlgebra.mapDomainAlgHom O O H.subtype (MonoidAlgebra.single h (1 : O)) =
        MonoidAlgebra.single (h : G) (1 : O) := by simp
    have := congrArg (MonoidAlgebra.mapDomainAlgHom O O H.subtype)
      (TauCeti.charIdempotent_mul_single χ h)
    rwa [map_mul, map_smul, hh] at this
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, map_add, mul_add, hx, hy]
  | single g a =>
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.surjective g
    dsimp only
    have hp : MonoidAlgebra.mapDomainAlgHom O O P.subtype
        (MonoidAlgebra.single p (a * (χ h : O))) =
        MonoidAlgebra.single (p : G) (a * (χ h : O)) := by simp
    have hsplit : MonoidAlgebra.single ((p : G) * (h : G)) a =
        a • (MonoidAlgebra.single (h : G) (1 : O) * MonoidAlgebra.single (p : G) (1 : O)) := by
      simp [MonoidAlgebra.single_mul_single, mul_comm (h : G), MonoidAlgebra.smul_single]
    rw [componentProj_single_mul, hp, hsplit, mul_smul_comm, ← mul_assoc, he_mul h,
      smul_mul_assoc, smul_comm, ← mul_smul_comm, MonoidAlgebra.smul_single, ← mul_smul_comm,
      MonoidAlgebra.smul_single]
    simp [mul_comm]

/-- Over any commutative ring `O` in which `#H` is a unit, the kernel of
`componentProj hPH χ : O[G] →ₐ[O] O[P]` is the principal ideal `(1 - e_χ)` generated by the
complementary idempotent of `χ`. -/
theorem ker_componentProj [Fintype H] (hPH : P.IsComplement' H)
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (componentProj hPH χ) =
      Ideal.span
        {(1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ))} := by
  let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · rw [RingHom.mem_ker] at hx
    have hex : e * x = 0 := by
      rw [charIdempotent_mul_eq_mul_mapDomain_componentProj hPH χ x, hx, map_zero, mul_zero]
    exact Ideal.mem_span_singleton.mpr ⟨x, by rw [sub_mul, one_mul, hex, sub_zero]⟩
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, componentProj_mapDomainAlgHom_right,
      χ.charEval_charIdempotent_self hH, map_one, sub_self]

section Domain

variable [IsDomain O] [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- For complementary subgroups `P.IsComplement' H` of a finite commutative group `G` and a domain
`O` with enough roots of unity, `α_{Ψ_χ}` and `componentProj hPH χ` have the same kernel, even
when `#H` is not a unit in `O`. -/
theorem ker_proj_eq_ker_componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) =
      RingHom.ker (componentProj hPH χ) := by
  have : HasEnoughRootsOfUnity O (Monoid.exponent P) :=
    .of_dvd O (Monoid.exponent_dvd_of_monoidHom P.subtype P.subtype_injective)
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, proj_eq_zero_iff]
  constructor
  · intro hx
    refine TauCeti.eq_of_forall_charEval_eq fun φ ↦ ?_
    rw [map_zero, charEval_componentProj]
    exact hx (extendChar hPH φ χ) (extendChar_comp_right hPH φ χ)
  · intro hx ψ hψ
    rw [← extendChar_comp_self hPH ψ, hψ, ← charEval_componentProj, hx, map_zero]

/-- **The `χ`-component character group ring is isomorphic to `O[P]`** (Dasgupta–Kakde, §2.3): for
complementary subgroups `P.IsComplement' H` of a finite commutative group `G` and a domain `O` with
enough roots of unity, `R_{Ψ_χ} ≃ₐ[O] O[P]`. No invertibility hypothesis on `#H` is required. -/
noncomputable def componentEquiv (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing ≃ₐ[O] MonoidAlgebra O P :=
  (Ideal.quotientKerAlgEquivOfSurjective (proj_surjective _)).symm.trans <|
    (Ideal.quotientEquivAlgOfEq O (ker_proj_eq_ker_componentProj hPH χ)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (componentProj_surjective hPH χ))

/-- `componentEquiv` sends `α_{Ψ_χ}(x)` to `componentProj hPH χ x`. -/
@[simp]
theorem componentEquiv_proj (hPH : P.IsComplement' H) (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    componentEquiv hPH χ (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x) =
      componentProj hPH χ x := by
  rw [componentEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse of `componentEquiv` embeds `y ∈ O[P]` into `O[G]` and projects to `R_{Ψ_χ}`. -/
@[simp]
theorem componentEquiv_symm_apply (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    (componentEquiv hPH χ).symm y =
      proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (MonoidAlgebra.mapDomainAlgHom O O P.subtype y) := by
  apply (componentEquiv hPH χ).injective
  rw [AlgEquiv.apply_symm_apply, componentEquiv_proj, componentProj_mapDomainAlgHom_left]

-- When `H = ⊥` and `P = ⊤`, every character restricts to `1` on `⊥`, and `componentEquiv`
-- identifies `R_univ` with `O[⊤] ≃ₐ[O] O[G]`.
example :
    Nonempty
      ({ψ : G →* Oˣ | ψ.comp (⊥ : Subgroup G).subtype = 1}.charGroupRing ≃ₐ[O]
        MonoidAlgebra O G) :=
  ⟨(componentEquiv Subgroup.isComplement'_top_bot 1).trans
    (MonoidAlgebra.domCongr O O Subgroup.topEquiv)⟩

-- When `P = ⊥` and `H = ⊤` with `#G` a unit in `O`, `piComponentAlgEquiv` splits `O[G]` as the
-- product over all characters `χ : ⊤ →* Oˣ` of 1-character components, each isomorphic to `O[⊥]`.
example (hG : IsUnit (Nat.card (⊤ : Subgroup G) : O)) :
    Nonempty
      (MonoidAlgebra O G ≃ₐ[O] ∀ _ : (⊤ : Subgroup G) →* Oˣ, MonoidAlgebra O (⊥ : Subgroup G)) :=
  ⟨(piComponentAlgEquiv (⊤ : Subgroup G) hG).trans
    (AlgEquiv.piCongrRight fun χ ↦ componentEquiv Subgroup.isComplement'_bot_top χ)⟩

-- For the cyclic group `ℤˣ` of order `2` and any domain `R` with enough roots of unity in which
-- `2` is a unit, the sign character `χ : ℤˣ →* Rˣ` sending `-1 ↦ -1` has `ker α_{Ψ_χ} = (1 - e_χ)`.
example {R : Type*} [CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent ℤˣ)]
    (h2 : IsUnit (2 : R)) :
    letI := Fintype.ofFinite (⊤ : Subgroup ℤˣ)
    let χ : (⊤ : Subgroup ℤˣ) →* Rˣ :=
      (Units.map (Int.castRingHom R).toMonoidHom).comp Subgroup.topEquiv.toMonoidHom
    RingHom.ker (proj {ψ : ℤˣ →* Rˣ | ψ.comp (⊤ : Subgroup ℤˣ).subtype = χ}) =
      Ideal.span {(1 - MonoidAlgebra.mapDomainAlgHom R R (⊤ : Subgroup ℤˣ).subtype
        (TauCeti.charIdempotent χ))} := by
  let := Fintype.ofFinite (⊤ : Subgroup ℤˣ)
  intro χ
  have hcard_nat : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcard : (Nat.card (⊤ : Subgroup ℤˣ) : R) = 2 := by
    rw [Subgroup.card_top, hcard_nat, Nat.cast_two]
  exact ker_proj_eq_span_one_sub_charIdempotent (⊤ : Subgroup ℤˣ) (hcard ▸ h2) χ

end Domain

end Complement

end Set.charGroupRing
