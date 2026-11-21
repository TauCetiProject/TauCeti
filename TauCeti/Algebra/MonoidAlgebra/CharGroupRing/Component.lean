/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Norm
public import TauCeti.GroupTheory.Complement.Prod
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Character components of group rings as character group rings

Let `O` be a commutative ring (or commutative semiring, where subtraction is not needed), `G` a
commutative group, `H` a subgroup of `G`, and `χ : H →* Oˣ` a character of `H`. Let
`Ψ_χ = {ψ : G →* Oˣ | ψ.comp H.subtype = χ}` be the set of characters of `G` extending `χ`.
Following Dasgupta and Kakde (§2.2), this file relates the character group ring `R_{Ψ_χ}` to
character idempotents, norm quotients, and complementary subgroup rings:

* **Idempotent description and product decomposition** (when `H` is finite and `#H` is a unit in
  `O`): the embedded character idempotent `e_χ = (#H)⁻¹ ∑_{h ∈ H} χ(h)⁻¹ h ∈ O[G]` evaluates to `1`
  on `Ψ_χ`, and when `O` is a domain it evaluates to `0` on every other character of `G`. When `G`
  is finite and `O` is a domain with enough roots of unity of order `exponent G`,
  `ker α_{Ψ_χ} = (1 - e_χ)` and the projections assemble into an `O`-algebra isomorphism
  `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` (`Set.charGroupRing.piComponentAlgEquiv`). Neither a complement to `H`
  in `G` nor any hypothesis on the quotient `G / H` is required here.
* **Norm quotients of a component** (Dasgupta–Kakde, Corollary 2.3): for a finite commutative group
  `G`, a domain `O` with enough roots of unity of order `exponent G`, and any two subgroups
  `H, I ≤ G` with `#H` a unit in `O`, the quotient of `R_{Ψ_χ}` by the image of the norm element
  `N_I = ∑_{σ ∈ I} σ` is canonically isomorphic to `R_{Ψ_χ ∩ Ψ_I}`, where
  `Ψ_I = {ψ | ¬ I ≤ ψ.ker}` (`Set.charGroupRing.componentQuotientSpanNormAlgEquiv`).
* **Complementary subgroup isomorphism** (`R_{Ψ_χ} ≃ₐ[O] O[P]`): when `P` and `H` are complementary
  subgroups of `G` (`P.IsComplement' H`, e.g. `G = G_p × G'`), sending `p * h ↦ χ(h) p` defines a
  surjective `O`-algebra homomorphism `componentProj : O[G] →ₐ[O] O[P]` over any commutative
  semiring `O`. Over any commutative ring in which `#H` is a unit, its kernel is `(1 - e_χ)`
  (`Set.charGroupRing.ker_componentProj`). Over a domain with enough roots of unity of order
  `exponent P` for finite `P`, `R_{Ψ_χ} ≃ₐ[O] O[P]` holds *without* assuming that `#H` is a unit
  in `O` (`Set.charGroupRing.componentEquiv`), because characters of `P` pair bijectively with
  members of `Ψ_χ` via `Subgroup.IsComplement'.extendChar`.

## Main definitions

* `Set.charGroupRing.piComponentAlgEquiv`: for finite `G` and a domain `O` with enough roots of
  unity, the decomposition `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` when `#H` is a unit in `O`.
* `Set.charGroupRing.componentQuotientSpanNormAlgEquiv`: for finite `G` and a domain `O` with
  enough roots of unity, the norm-quotient isomorphism
  `R_{Ψ_χ} / (α_{Ψ_χ}(N_I)) ≃ₐ[O] R_{Ψ_χ ∩ Ψ_I}` when `#H` is a unit in `O`
  (Dasgupta–Kakde, Corollary 2.3).
* `Set.charGroupRing.componentProj`: the `χ`-twisted projection `O[G] →ₐ[O] O[P]` sending
  `p * h ↦ χ(h) p`.
* `Set.charGroupRing.componentEquiv`: for finite `P` and a domain `O` with enough roots of unity of
  order `exponent P`, the `O`-algebra isomorphism `R_{Ψ_χ} ≃ₐ[O] O[P]`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.2
  (Corollary 2.3).
-/

public section

namespace MonoidHom

section CommRing

variable {O H G : Type*} [CommRing O] [CommGroup H] [Fintype H] [CommGroup G]

private theorem charIdempotent_eq_smul_subgroupCharSum (χ : H →* Oˣ) :
    TauCeti.charIdempotent χ =
      letI := Fintype.ofFinite (⊤ : Subgroup H)
      Ring.inverse (Nat.card H : O) •
        TauCeti.subgroupCharSum ((Units.coeHom O).comp χ⁻¹) (⊤ : Subgroup H) := by
  let := Fintype.ofFinite (⊤ : Subgroup H)
  rw [TauCeti.charIdempotent_eq_sum, TauCeti.subgroupCharSum_eq_sum_of_eq_top _ _ rfl]
  simp

/-- When `#H` is a unit in `O`, a character `χ` evaluates to `1` on its own character idempotent
`e_χ`. No domain hypothesis on `O` is required. -/
theorem charEval_charIdempotent_self (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    χ.charEval (TauCeti.charIdempotent χ) = 1 := by
  let := Fintype.ofFinite (⊤ : Subgroup H)
  rw [charIdempotent_eq_smul_subgroupCharSum, map_smul,
    MonoidHom.charEval_subgroupCharSum_of_le_ker χ⁻¹ χ ⊤ (fun h _ ↦ by simp [MonoidHom.mem_ker]),
    Subgroup.card_top, smul_eq_mul, Ring.inverse_mul_cancel _ hH]

/-- Over a domain, a character `ψ` vanishes on the character idempotent `e_χ` of any distinct
character `χ ≠ ψ`. No unit hypothesis on `#H` is required. -/
theorem charEval_charIdempotent_of_ne [IsDomain O] {χ ψ : H →* Oˣ} (h : χ ≠ ψ) :
    ψ.charEval (TauCeti.charIdempotent χ) = 0 := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup H)
  rw [charIdempotent_eq_smul_subgroupCharSum, map_smul,
    MonoidHom.charEval_subgroupCharSum_inv_top, ite_eq_right h, smul_zero]

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

section ComponentSets

variable {O G : Type*} [CommSemiring O] [CommGroup G]

/-- Inclusion of `Ψ_χ ∩ Ψ_I` into `Ψ_χ`. -/
theorem componentNorm_subset (H I : Subgroup G) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker} ⊆
      {ψ : G →* Oˣ | ψ.comp H.subtype = χ} :=
  fun _ h ↦ h.1

/-- For subgroups `H, I` of a finite commutative group `G` and a commutative semiring `O` with
enough roots of unity of order `exponent G`, there exists a character of `G` extending `χ : H →* Oˣ`
that is nontrivial on `I` if and only if `I` is not contained in `χ.ker.map H.subtype`. -/
theorem nonempty_componentNormSet_iff [Finite G]
    [HasEnoughRootsOfUnity O (Monoid.exponent G)] (H I : Subgroup G) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}.Nonempty ↔
      ¬ I ≤ χ.ker.map H.subtype := by
  constructor
  · rintro ⟨ψ, hψ, hI⟩ hle
    refine hI fun g hg ↦ ?_
    obtain ⟨h, hh, rfl⟩ := hle hg
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hψ]
    exact MonoidHom.mem_ker.mp hh
  · intro hle
    obtain ⟨ψ₀, hψ₀⟩ := MonoidHom.domRestrict_surjective (M := O) H χ
    have hψ₀' : ψ₀.comp H.subtype = χ := MonoidHom.ext fun h ↦ by
      simpa [MonoidHom.domRestrictHom_apply] using DFunLike.congr_fun hψ₀ h
    by_cases hI : I ≤ ψ₀.ker
    · obtain ⟨g, hgI, hgker⟩ := IsConcreteLE.not_le_iff_exists.mp hle
      have hgH : g ∉ H := fun hgH ↦ hgker ⟨⟨g, hgH⟩, by
        rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hψ₀', MonoidHom.comp_apply, Subgroup.coe_subtype]
        exact MonoidHom.mem_ker.mp (hI hgI), rfl⟩
      have hex := (CommGroup.forall_monoidHom_apply_eq_one_iff (M := O) H g).not.mpr hgH
      push Not at hex
      obtain ⟨φ, hφH, hφg⟩ := hex
      refine ⟨φ * ψ₀, ?_, fun hle' ↦ hφg ?_⟩
      · refine MonoidHom.ext fun h ↦ ?_
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.mul_apply, hφH h h.2, one_mul,
          ← Subgroup.coe_subtype, ← MonoidHom.comp_apply, hψ₀']
      · have h1 := MonoidHom.mem_ker.mp (hle' hgI)
        rw [MonoidHom.mul_apply, MonoidHom.mem_ker.mp (hI hgI), mul_one] at h1
        exact h1
    · exact ⟨ψ₀, hψ₀', hI⟩

end ComponentSets

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

/-- For a finite commutative group `G`, a domain `O` with enough roots of unity of order
`exponent G`, a subgroup `H` with `#H` a unit in `O`, and a character `χ : H →* Oˣ`, the kernel of
`α_{Ψ_χ} : O[G] → R_{Ψ_χ}` is the principal ideal `(1 - e_χ)` generated by the complementary
idempotent of `χ`. -/
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

private theorem bijective_pi_proj (H : Subgroup G) (hH : IsUnit (Nat.card H : O)) :
    Function.Bijective
      (AlgHom.pi fun χ : H →* Oˣ ↦ proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) := by
  classical
  let := Fintype.ofFinite H
  let := Fintype.ofFinite (H →* Oˣ)
  refine ⟨?_, ?_⟩
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
      have hψ' : ψ.comp H.subtype = χ₀ := Set.mem_ofPred_eq.mp hψ
      rw [map_mul, MonoidHom.charEval_mapDomainAlgHom_charIdempotent H hH, hψ']
      split_ifs <;> simp
    have hfx : ψ.charEval (x χ₀) =
        (f χ₀ : {ψ' : G →* Oˣ | ψ'.comp H.subtype = χ₀} → O) ⟨ψ, hψ⟩ := by
      rw [← hx χ₀, coe_proj_apply]
    rw [AlgHom.pi_apply, coe_proj_apply, map_sum]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hfx]

/-- **Decomposition of a group ring into character components**: for a finite commutative group `G`,
a domain `O` with enough roots of unity of order `exponent G`, and a subgroup `H ≤ G` whose order is
invertible in `O`, the product of the canonical projections `α_{Ψ_χ} : O[G] → R_{Ψ_χ}` over all
`χ : H →* Oˣ` is an `O`-algebra isomorphism `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}`. -/
noncomputable def piComponentAlgEquiv (H : Subgroup G)
    (hH : IsUnit (Nat.card H : O)) :
    MonoidAlgebra O G ≃ₐ[O] ∀ χ : H →* Oˣ, {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing :=
  AlgEquiv.ofBijective _ (bijective_pi_proj H hH)

/-- The `χ`-coordinate of `piComponentAlgEquiv` is the projection `α_{Ψ_χ}`. -/
@[simp]
theorem piComponentAlgEquiv_apply (H : Subgroup G) (hH : IsUnit (Nat.card H : O))
    (x : MonoidAlgebra O G) (χ : H →* Oˣ) :
    piComponentAlgEquiv H hH x χ = proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x := by
  simp [piComponentAlgEquiv]

/-- Projecting `(piComponentAlgEquiv H hH).symm f` onto the `χ`-component recovers `f χ`. -/
@[simp]
theorem proj_piComponentAlgEquiv_symm (H : Subgroup G) (hH : IsUnit (Nat.card H : O))
    (f : ∀ χ : H →* Oˣ, {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) (χ : H →* Oˣ) :
    proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} ((piComponentAlgEquiv H hH).symm f) = f χ :=
  congr_fun ((piComponentAlgEquiv H hH).apply_symm_apply f) χ

/-- Evaluating `(piComponentAlgEquiv H hH).symm f` at any character `ψ : G →* Oˣ` reads off the
`ψ`-coordinate of `f (ψ.comp H.subtype)`. -/
@[simp]
theorem charEval_piComponentAlgEquiv_symm (H : Subgroup G) (hH : IsUnit (Nat.card H : O))
    (f : ∀ χ : H →* Oˣ, {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) (ψ : G →* Oˣ) :
    ψ.charEval ((piComponentAlgEquiv H hH).symm f) =
      (f (ψ.comp H.subtype) :
        {ψ' : G →* Oˣ | ψ'.comp H.subtype = ψ.comp H.subtype} → O) ⟨ψ, rfl⟩ := by
  rw [← coe_proj_apply (Ψ := {ψ' : G →* Oˣ | ψ'.comp H.subtype = ψ.comp H.subtype}) _ ⟨ψ, rfl⟩,
    proj_piComponentAlgEquiv_symm]

/-- **Kernel of a norm-and-component character group ring** (Dasgupta–Kakde, Corollary 2.3): for a
finite commutative group `G`, a domain `O` with enough roots of unity of order `exponent G`, and
subgroups `H, I ≤ G` with `#H` a unit in `O`, the kernel of `α_Ψ` for
`Ψ = {ψ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}` is generated by `1 - e_χ` and the subgroup norm
`N_I = ∑_{σ ∈ I} σ`. -/
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
      exact proj_eq_zero_iff.mp (RingHom.mem_ker.mp (one_sub_charIdempotent_mem_ker_proj H hH χ))
        ψ hψ.1
    · rw [Set.mem_singleton_iff.mp hN, SetLike.mem_coe, RingHom.mem_ker, proj_eq_zero_iff]
      intro ψ hψ
      exact ψ.charEval_subgroupCharSum_one_eq_zero I hψ.2

/-- For a finite commutative group `G`, a domain `O` with enough roots of unity of order
`exponent G`, and subgroups `H, I ≤ G` with `#H` a unit in `O`, the kernel of the restriction
`R_{Ψ_χ} → R_{Ψ_χ ∩ Ψ_I}` is the principal ideal generated by `α_{Ψ_χ}(N_I)`. -/
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
      RingHom.mem_ker.mp (one_sub_charIdempotent_mem_ker_proj H hH χ)
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
Corollary 2.3): for a finite commutative group `G`, a domain `O` with enough roots of unity of
order `exponent G`, and subgroups `H, I ≤ G` with `#H` a unit in `O`, dividing the `χ`-component
`R_{Ψ_χ}` by the image of the norm element `N_I = ∑_{σ ∈ I} σ` yields the character group ring
`R_{Ψ_χ ∩ Ψ_I}` of characters extending `χ` that are nontrivial on `I`. -/
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
      restrictAlgHom (componentNorm_subset H I χ) y := by
  simp [componentQuotientSpanNormAlgEquiv]

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

section CommSemiring

variable {O G : Type*} [CommSemiring O] [CommGroup G] {P H : Subgroup G}

/-- For complementary subgroups `P.IsComplement' H`, the `χ`-component character set
`{ψ : G →* Oˣ | ψ.comp H.subtype = χ}` is always nonempty, witnessed by `hPH.extendChar 1 χ`. -/
theorem nonempty_componentSet (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.Nonempty :=
  ⟨hPH.extendChar 1 χ, hPH.extendChar_comp_right 1 χ⟩

/-- For complementary subgroups `P.IsComplement' H` of a finite commutative group `G` and any
nontrivial subgroup `I ≤ P`, when `O` has enough roots of unity of order `exponent G`, there exists
a character of `G` extending `χ` that is nontrivial on `I`. -/
theorem nonempty_componentNormSet [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]
    {I : Subgroup G} (hPH : P.IsComplement' H) (hIP : I ≤ P) (hI : I ≠ ⊥) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}.Nonempty :=
  (nonempty_componentNormSet_iff H I χ).mpr fun hle ↦
    hI <| le_bot_iff.mp <| hPH.disjoint.eq_bot ▸ le_inf hIP (hle.trans (Subgroup.map_subtype_le _))

/-- **The `χ`-component projection `O[G] →ₐ[O] O[P]`** across complementary subgroups
`P.IsComplement' H`: the `O`-algebra homomorphism sending `(p : G) * (h : G)` to `χ(h) • p` for
`p ∈ P` and `h ∈ H` (Dasgupta–Kakde, §2.2). -/
noncomputable def componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    MonoidAlgebra O G →ₐ[O] MonoidAlgebra O P :=
  let f : P × H →* MonoidAlgebra O P :=
    MonoidAlgebra.singleHom.comp
      ((((Units.coeHom O).comp χ).comp (MonoidHom.snd P H)).prod (MonoidHom.fst P H))
  MonoidAlgebra.lift O (MonoidAlgebra O P) G (f.comp hPH.prodMulEquiv.symm.toMonoidHom)

/-- `componentProj` sends `single (p * h) a` to `single p (a * χ(h))` for `p ∈ P` and `h ∈ H`. -/
@[simp]
theorem componentProj_single_mul (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (p : P) (h : H) (a : O) :
    componentProj hPH χ (MonoidAlgebra.single ((p : G) * (h : G)) a) =
      MonoidAlgebra.single p (a * (χ h : O)) := by
  simp [componentProj, Subgroup.IsComplement'.prodMulEquiv_symm_mul, MonoidAlgebra.smul_single]

/-- `componentProj` sends `single (p : G) a` for `p : P` to `single p a`. -/
@[simp]
theorem componentProj_single_left (hPH : P.IsComplement' H) (χ : H →* Oˣ) (p : P) (a : O) :
    componentProj hPH χ (MonoidAlgebra.single (p : G) a) = MonoidAlgebra.single p a := by
  simpa using componentProj_single_mul hPH χ p 1 a

/-- `componentProj` sends `single (h : G) a` for `h : H` to `single 1 (a * χ(h))`. -/
@[simp]
theorem componentProj_single_right (hPH : P.IsComplement' H) (χ : H →* Oˣ) (h : H) (a : O) :
    componentProj hPH χ (MonoidAlgebra.single (h : G) a) =
      MonoidAlgebra.single 1 (a * (χ h : O)) := by
  simpa using componentProj_single_mul hPH χ 1 h a

/-- Applying `componentProj` to an element embedded from `O[P]` via `mapDomain Subtype.val`
recovers it. -/
@[simp]
theorem componentProj_mapDomain_left (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    componentProj hPH χ (MonoidAlgebra.mapDomain (Subtype.val : P → G) y) = y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [MonoidAlgebra.mapDomain_add, map_add, hx, hy]
  | single p a => simp

/-- Applying `componentProj` to an element pushed forward from `O[P]` recovers it. -/
theorem componentProj_mapDomainAlgHom_left (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O P.subtype y) = y := by
  simp

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

/-- On `O[H]` embedded into `O[G]` via `mapDomain Subtype.val`, `componentProj hPH χ` acts as
`single 1 (χ.charEval y)`. -/
@[simp]
theorem componentProj_mapDomain_right (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O H) :
    componentProj hPH χ (MonoidAlgebra.mapDomain (Subtype.val : H → G) y) =
      MonoidAlgebra.single 1 (χ.charEval y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [MonoidAlgebra.mapDomain_add, map_add, map_add, MonoidAlgebra.single_add,
      hx, hy]
  | single h a => simp

/-- On `O[H] ⊆ O[G]`, `componentProj hPH χ` acts as scalar evaluation `χ.charEval` followed by
`algebraMap O O[P]`. -/
theorem componentProj_mapDomainAlgHom_right (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O H) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O H.subtype y) =
      algebraMap O (MonoidAlgebra O P) (χ.charEval y) := by
  simp

/-- Evaluating `componentProj hPH χ x` at a character `φ : P →* Oˣ` agrees with evaluating `x` at
the extended character `hPH.extendChar φ χ : G →* Oˣ`. -/
@[simp]
theorem charEval_componentProj (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ)
    (x : MonoidAlgebra O G) :
    φ.charEval (componentProj hPH χ x) = (hPH.extendChar φ χ).charEval x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a =>
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    rw [Subgroup.IsComplement'.prodMulEquiv_apply]
    simp [mul_assoc, mul_comm (χ h : O)]

end CommSemiring

section CommRing

variable {O G : Type*} [CommRing O] [CommGroup G] {P H : Subgroup G}

/-- When `#H` is a unit in `O`, `componentProj hPH χ` sends the embedded character idempotent
`e_χ` to `1`. No domain hypothesis on `O` is required. -/
theorem componentProj_mapDomainAlgHom_charIdempotent_self [Fintype H] (hPH : P.IsComplement' H)
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) =
      1 := by
  rw [componentProj_mapDomainAlgHom_right, χ.charEval_charIdempotent_self hH, map_one]

/-- Over a domain, `componentProj hPH χ` kills the embedded character idempotent `e_ω` of any
distinct character `ω ≠ χ`. No unit hypothesis on `#H` is required. -/
theorem componentProj_mapDomainAlgHom_charIdempotent_of_ne [IsDomain O] [Fintype H]
    (hPH : P.IsComplement' H) {χ ω : H →* Oˣ} (h : ω ≠ χ) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent ω)) =
      0 := by
  rw [componentProj_mapDomainAlgHom_right, MonoidHom.charEval_charIdempotent_of_ne h, map_zero]

/-- Over a domain in which `#H` is a unit, `componentProj hPH χ` sends the embedded character
idempotent `e_ω` to `1` if `ω = χ` and to `0` otherwise. -/
theorem componentProj_mapDomainAlgHom_charIdempotent [IsDomain O] [Fintype H]
    [DecidableEq (H →* Oˣ)] (hPH : P.IsComplement' H) (hH : IsUnit (Nat.card H : O))
    (χ ω : H →* Oˣ) :
    componentProj hPH χ (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent ω)) =
      if ω = χ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact componentProj_mapDomainAlgHom_charIdempotent_self hPH hH ω
  · exact componentProj_mapDomainAlgHom_charIdempotent_of_ne hPH h

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
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    rw [Subgroup.IsComplement'.prodMulEquiv_apply]
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
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      componentProj_mapDomainAlgHom_charIdempotent_self hPH hH χ, sub_self]

section Domain

variable [IsDomain O] [Finite P] [HasEnoughRootsOfUnity O (Monoid.exponent P)]

/-- For complementary subgroups `P.IsComplement' H` with `P` finite and a domain `O` with enough
roots of unity of order `exponent P`, `α_{Ψ_χ}` and `componentProj hPH χ` have the same kernel,
even when `H` is infinite or `#H` is not a unit in `O`. -/
theorem ker_proj_eq_ker_componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) =
      RingHom.ker (componentProj hPH χ) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, proj_eq_zero_iff]
  constructor
  · intro hx
    refine TauCeti.eq_of_forall_charEval_eq fun φ ↦ ?_
    rw [map_zero, charEval_componentProj]
    exact hx (hPH.extendChar φ χ) (hPH.extendChar_comp_right φ χ)
  · intro hx ψ hψ
    rw [← hPH.extendChar_comp_self ψ, hψ, ← charEval_componentProj, hx, map_zero]

/-- **The `χ`-component character group ring is isomorphic to `O[P]`** (Dasgupta–Kakde, §2.2): for
complementary subgroups `P.IsComplement' H` with `P` finite and a domain `O` with enough roots of
unity of order `exponent P`, `R_{Ψ_χ} ≃ₐ[O] O[P]`. No finiteness or invertibility hypothesis on
`H` is required. -/
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

/-- Evaluating `componentEquiv hPH χ y` at a character `φ : P →* Oˣ` reads off the
`hPH.extendChar φ χ`-coordinate of `y`. -/
@[simp]
theorem charEval_componentEquiv (hPH : P.IsComplement' H) (χ : H →* Oˣ) (φ : P →* Oˣ)
    (y : {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) :
    φ.charEval (componentEquiv hPH χ y) =
      (y : {ψ : G →* Oˣ | ψ.comp H.subtype = χ} → O)
        ⟨hPH.extendChar φ χ, hPH.extendChar_comp_right φ χ⟩ := by
  obtain ⟨x, rfl⟩ := proj_surjective _ y
  rw [componentEquiv_proj, charEval_componentProj, coe_proj_apply]

section Examples

omit [Finite P] [HasEnoughRootsOfUnity O (Monoid.exponent P)] in
-- When `H = ⊥` and `P = ⊤`, every character restricts to `1` on `⊥`, and `componentEquiv`
-- identifies `R_univ` with `O[⊤] ≃ₐ[O] O[G]`.
example [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)] :
    Nonempty
      ({ψ : G →* Oˣ | ψ.comp (⊥ : Subgroup G).subtype = 1}.charGroupRing ≃ₐ[O]
        MonoidAlgebra O G) := by
  have : HasEnoughRootsOfUnity O (Monoid.exponent (⊤ : Subgroup G)) :=
    .of_dvd O (Monoid.exponent_dvd_of_monoidHom _ (⊤ : Subgroup G).subtype_injective)
  exact ⟨(componentEquiv Subgroup.isComplement'_top_bot 1).trans
    (MonoidAlgebra.domCongr O O Subgroup.topEquiv)⟩

omit [Finite P] [HasEnoughRootsOfUnity O (Monoid.exponent P)] in
-- When `P = ⊥` and `H = ⊤` with `#G` a unit in `O`, `piComponentAlgEquiv` splits `O[G]` as the
-- product over all characters `χ : ⊤ →* Oˣ` of 1-character components, each isomorphic to `O[⊥]`.
example [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]
    (hG : IsUnit (Nat.card (⊤ : Subgroup G) : O)) :
    Nonempty
      (MonoidAlgebra O G ≃ₐ[O] ∀ _ : (⊤ : Subgroup G) →* Oˣ, MonoidAlgebra O (⊥ : Subgroup G)) := by
  have : HasEnoughRootsOfUnity O (Monoid.exponent (⊥ : Subgroup G)) :=
    .of_dvd O (Monoid.exponent_dvd_of_monoidHom _ (⊥ : Subgroup G).subtype_injective)
  exact ⟨(piComponentAlgEquiv (⊤ : Subgroup G) hG).trans
    (AlgEquiv.piCongrRight fun χ ↦ componentEquiv Subgroup.isComplement'_bot_top χ)⟩

end Examples

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

end CommRing

end Complement

end Set.charGroupRing
