/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Norm
public import TauCeti.Algebra.MonoidAlgebra.TwistedProj
public import TauCeti.RingTheory.Idempotents.Corner.Basic

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
  `ker α_{Ψ_χ} = (1 - e_χ)`, `R_{Ψ_χ}` is canonically isomorphic to the idempotent corner
  `e_χ O[G] e_χ` (`Set.charGroupRing.componentCornerAlgEquiv`), and the projections assemble into
  an `O`-algebra isomorphism `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` (`Set.charGroupRing.piComponentAlgEquiv`).
  Neither a complement to `H` in `G` nor any hypothesis on the quotient `G / H` is required here.
* **Norm quotients of a component** (Dasgupta–Kakde, Corollary 2.3): for a finite commutative group
  `G`, a domain `O` with enough roots of unity of order `exponent G`, and any two subgroups
  `H, I ≤ G` with `#H` a unit in `O`, the quotient of `R_{Ψ_χ}` by the image of the norm element
  `N_I = ∑_{σ ∈ I} σ` is canonically isomorphic to `R_{Ψ_χ ∩ Ψ_I}`, where
  `Ψ_I = {ψ | ¬ I ≤ ψ.ker}` (`Set.charGroupRing.componentQuotientSpanNormAlgEquiv`).
* **Complementary subgroup isomorphism** (`R_{Ψ_χ} ≃ₐ[O] O[P]`): when `P` and `H` are complementary
  subgroups of `G` (`P.IsComplement' H`, e.g. `G = G_p × G'`), the `χ`-twisted projection
  `MonoidAlgebra.componentProj hPH χ : O[G] →ₐ[O] O[P]` compares directly with `proj` and induces
  `R_{Ψ_χ} ≃ₐ[O] O[P]` over a domain with enough roots of unity of order `exponent P` for finite
  `P` *without* assuming that `#H` is a unit in `O` (`Set.charGroupRing.componentEquiv`), because
  characters of `P` pair bijectively with members of `Ψ_χ` via `Subgroup.IsComplement'.extendChar`.

## Main definitions

* `Set.charGroupRing.componentCornerAlgEquiv`: for finite `G` and a domain `O` with enough roots of
  unity, the identification `R_{Ψ_χ} ≃ₐ[O] e_χ O[G] e_χ` with the idempotent corner when `#H` is
  a unit in `O`.
* `Set.charGroupRing.piComponentAlgEquiv`: for finite `G` and a domain `O` with enough roots of
  unity, the decomposition `O[G] ≃ₐ[O] ∏_χ R_{Ψ_χ}` when `#H` is a unit in `O`.
* `Set.charGroupRing.componentQuotientSpanNormAlgEquiv`: for finite `G` and a domain `O` with
  enough roots of unity, the norm-quotient isomorphism
  `R_{Ψ_χ} / (α_{Ψ_χ}(N_I)) ≃ₐ[O] R_{Ψ_χ ∩ Ψ_I}` when `#H` is a unit in `O`
  (Dasgupta–Kakde, Corollary 2.3).
* `Set.charGroupRing.componentEquiv`: for finite `P` and a domain `O` with enough roots of unity of
  order `exponent P`, the `O`-algebra isomorphism `R_{Ψ_χ} ≃ₐ[O] O[P]`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.2
  (Corollary 2.3).
-/

public section

namespace Set.charGroupRing

section ComponentSets

variable {O G : Type*} [CommSemiring O] [CommGroup G]

/-- Inclusion of `Ψ_χ ∩ Ψ_I` into `Ψ_χ`. -/
theorem componentNorm_subset (H I : Subgroup G) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker} ⊆
      {ψ : G →* Oˣ | ψ.comp H.subtype = χ} :=
  fun _ h ↦ h.left

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
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.mul_apply, hφH h h.property,
          one_mul, ← Subgroup.coe_subtype, ← MonoidHom.comp_apply, hψ₀']
      · have h1 := MonoidHom.mem_ker.mp (hle' hgI)
        rw [MonoidHom.mul_apply, MonoidHom.mem_ker.mp (hI hgI), mul_one] at h1
        exact h1
    · exact ⟨ψ₀, hψ₀', hI⟩

end ComponentSets

section IdempotentAndNorm

variable {O G : Type*} [CommRing O] [CommGroup G]

/-- The embedded character idempotent `e_χ ∈ O[G]` of `χ : H →* Oˣ` is idempotent. -/
theorem isIdempotentElem_mapDomainAlgHom_charIdempotent (H : Subgroup G) [Fintype H]
    (χ : H →* Oˣ) :
    IsIdempotentElem
      (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) :=
  (TauCeti.isIdempotentElem_charIdempotent χ).map _

/-- Compression `x ↦ e_χ * x * e_χ` from `O[G]` onto the idempotent corner of `e_χ`. -/
private noncomputable def compressCharIdempotentAlgHom (H : Subgroup G) [Fintype H]
    (χ : H →* Oˣ) :
    MonoidAlgebra O G →ₐ[O] (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).Corner where
  toFun := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress
  map_one' := Subtype.ext <| by
    simp only [IsIdempotentElem.Corner.val_one, IsIdempotentElem.val_compress, mul_one]
    exact (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).eq
  map_mul' x y := Subtype.ext <| by
    let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
    have he := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).eq
    simp only [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.val_compress]
    change e * (x * y) * e = e * x * e * (e * y * e)
    calc
      e * (x * y) * e = (e * e) * (x * y) * (e * e) := by rw [he]
      _ = e * x * e * (e * y * e) := by ring
  map_zero' := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress_zero
  map_add' := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress_add
  commutes' r := Subtype.ext <| by
    let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
    have he := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).eq
    simp only [IsIdempotentElem.Corner.val_algebraMap, IsIdempotentElem.val_compress,
      Algebra.smul_def]
    change e * (algebraMap O (MonoidAlgebra O G) r) * e = algebraMap O (MonoidAlgebra O G) r * e
    calc
      e * algebraMap O (MonoidAlgebra O G) r * e =
          algebraMap O (MonoidAlgebra O G) r * (e * e) := by ring
      _ = algebraMap O (MonoidAlgebra O G) r * e := by rw [he]

private theorem compressCharIdempotentAlgHom_apply (H : Subgroup G) [Fintype H]
    (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    compressCharIdempotentAlgHom H χ x =
      (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress x :=
  (rfl)

private theorem compressCharIdempotentAlgHom_surjective (H : Subgroup G) [Fintype H]
    (χ : H →* Oˣ) : Function.Surjective (compressCharIdempotentAlgHom H χ) :=
  fun b ↦ ⟨b.val, (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress_val b⟩

private theorem ker_compressCharIdempotentAlgHom (H : Subgroup G) [Fintype H] (χ : H →* Oˣ) :
    RingHom.ker (compressCharIdempotentAlgHom H χ) =
      Ideal.span
        {(1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ))} := by
  let e := MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  have he := (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).eq
  ext x
  rw [RingHom.mem_ker, compressCharIdempotentAlgHom_apply, Ideal.mem_span_singleton]
  have hexe : e * x * e = e * x := by
    calc
      e * x * e = (e * e) * x := by ring
      _ = e * x := by rw [he]
  constructor
  · intro hex
    have hex' := congrArg Subtype.val hex
    simp only [IsIdempotentElem.val_compress, IsIdempotentElem.Corner.val_zero] at hex'
    change e * x * e = 0 at hex'
    rw [hexe] at hex'
    exact ⟨x, by rw [sub_mul, one_mul, hex', sub_zero]⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    simp only [IsIdempotentElem.val_compress, IsIdempotentElem.Corner.val_zero]
    change e * ((1 - e) * y) * e = 0
    calc
      e * ((1 - e) * y) * e = (e - e * e) * y * e := by ring
      _ = 0 := by rw [he, sub_self, zero_mul, zero_mul]

/-- When `#H` is a unit in `O`, `1 - e_χ` vanishes on every character of `G` extending `χ`, where
`e_χ` is the character idempotent of `χ` pushed forward from `O[H]` to `O[G]`. -/
theorem one_sub_charIdempotent_mem_ker_proj (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) ∈
      RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) := by
  rw [RingHom.mem_ker, proj_eq_zero_iff]
  intro ψ hψ
  rw [map_sub, map_one, MonoidAlgebra.mapDomainAlgHom_apply, ψ.charEval_mapDomain, hψ,
    χ.charEval_charIdempotent_self hH, sub_self]

section DomainNoFin

variable [IsDomain O]

/-- Evaluating `α_{Ψ_χ ∩ Ψ_I}` at the subgroup norm `N_I = ∑_{σ ∈ I} σ` gives `0` when `O` is
a domain, with no invertibility assumption on `#H`. -/
@[simp]
theorem proj_componentNorm_subgroupCharSum_one_eq_zero (H I : Subgroup G) [Fintype I]
    (χ : H →* Oˣ) :
    proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}
      (TauCeti.subgroupCharSum (1 : G →* O) I) = 0 := by
  rw [proj_eq_zero_iff]
  intro ψ hψ
  exact ψ.charEval_subgroupCharSum_one_eq_zero I hψ.right

private theorem charEval_charIdempotent_mul_eq_zero_of_forall {S : Set (G →* Oˣ)}
    {H : Subgroup G} [Fintype H] {χ : H →* Oˣ} {x : MonoidAlgebra O G}
    (hx : ∀ ψ ∈ S, ψ.comp H.subtype = χ → ψ.charEval x = 0)
    {ψ : G →* Oˣ} (hψS : ψ ∈ S) :
    ψ.charEval (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x) =
      0 := by
  rw [map_mul]
  by_cases hψ : ψ.comp H.subtype = χ
  · rw [hx ψ hψS hψ, mul_zero]
  · simp only [MonoidAlgebra.mapDomainAlgHom_apply, MonoidHom.charEval_mapDomain,
      MonoidHom.charEval_charIdempotent_of_ne (Ne.symm hψ), zero_mul]

end DomainNoFin

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
    rw [map_zero]
    exact charEval_charIdempotent_mul_eq_zero_of_forall (fun ψ _ hψ ↦ hx ψ hψ) (Set.mem_univ ψ)
  exact Ideal.mem_span_singleton.mpr ⟨x, by rw [sub_mul, one_mul, hex, sub_zero]⟩

/-- **Idempotent corner description of a character component**: for a finite commutative group `G`,
a domain `O` with enough roots of unity of order `exponent G`, and a subgroup `H` with `#H` a unit
in `O`, the `χ`-component character group ring `R_{Ψ_χ}` is canonically isomorphic as an
`O`-algebra to the idempotent corner `e_χ O[G] e_χ`. -/
noncomputable def componentCornerAlgEquiv (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing ≃ₐ[O]
      (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).Corner :=
  (Ideal.quotientKerAlgEquivOfSurjective (proj_surjective _)).symm.trans <|
    (Ideal.quotientEquivAlgOfEq O
      ((ker_proj_eq_span_one_sub_charIdempotent H hH χ).trans
        (ker_compressCharIdempotentAlgHom H χ).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (compressCharIdempotentAlgHom_surjective H χ))

/-- `componentCornerAlgEquiv` sends `α_{Ψ_χ}(x)` to the compression of `x` by `e_χ`. -/
@[simp]
theorem componentCornerAlgEquiv_proj (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    componentCornerAlgEquiv H hH χ (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x) =
      (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress x := by
  rw [componentCornerAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk, compressCharIdempotentAlgHom_apply]

/-- The inverse of `componentCornerAlgEquiv` projects elements of the idempotent corner
`e_χ O[G] e_χ` to `R_{Ψ_χ}`. -/
@[simp]
theorem componentCornerAlgEquiv_symm_apply (H : Subgroup G) [Fintype H]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ)
    (b : (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).Corner) :
    (componentCornerAlgEquiv H hH χ).symm b =
      proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} b.val := by
  apply (componentCornerAlgEquiv H hH χ).injective
  rw [AlgEquiv.apply_symm_apply, componentCornerAlgEquiv_proj,
    (isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).compress_val]

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
      exact charEval_charIdempotent_mul_eq_zero_of_forall
        (fun ψ hI' hψ ↦ hx ψ ⟨hψ, hI'⟩) hI
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hex
    refine Ideal.mem_span_pair.mpr ⟨x, y, ?_⟩
    rw [mul_sub, mul_one, mul_comm x, hy, mul_comm y N, sub_add_cancel]
  · rintro z (rfl | hN)
    · rw [SetLike.mem_coe, RingHom.mem_ker, proj_eq_zero_iff]
      intro ψ hψ
      exact proj_eq_zero_iff.mp (RingHom.mem_ker.mp (one_sub_charIdempotent_mem_ker_proj H hH χ))
        ψ hψ.left
    · rw [Set.mem_singleton_iff.mp hN, SetLike.mem_coe, RingHom.mem_ker]
      exact proj_componentNorm_subgroupCharSum_one_eq_zero H I χ

/-- For a finite commutative group `G`, a domain `O` with enough roots of unity of order
`exponent G`, and subgroups `H, I ≤ G` with `#H` a unit in `O`, the kernel of the restriction
`R_{Ψ_χ} → R_{Ψ_χ ∩ Ψ_I}` is the principal ideal generated by `α_{Ψ_χ}(N_I)`. -/
theorem ker_restrictAlgHom_component_norm (H I : Subgroup G) [Fintype I]
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (restrictAlgHom (componentNorm_subset H I χ)) =
      Ideal.span {(proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (TauCeti.subgroupCharSum (1 : G →* O) I))} := by
  let := Fintype.ofFinite H
  rw [← Ideal.map_comap_of_surjective _
      (proj_surjective {ψ : G →* Oˣ | ψ.comp H.subtype = χ})
      (RingHom.ker (restrictAlgHom (componentNorm_subset H I χ))),
    AlgHom.comap_ker, restrictAlgHom_comp_proj, ker_proj_component_norm H I hH χ, Ideal.map_span]
  have hzero :
      proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}
        (1 - MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) = 0 :=
    RingHom.mem_ker.mp (one_sub_charIdempotent_mem_ker_proj H hH χ)
  simp only [Set.image_pair, hzero, Ideal.span_insert_zero]

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

/-- For complementary subgroups `P.IsComplement' H` of a commutative group `G` with `P` finite
and any nontrivial subgroup `I ≤ P`, when `O` has enough roots of unity of order `exponent P`,
there exists a character of `G` extending `χ` that is nontrivial on `I`. -/
theorem nonempty_componentNormSet [Finite P] [HasEnoughRootsOfUnity O (Monoid.exponent P)]
    {I : Subgroup G} (hPH : P.IsComplement' H) (hIP : I ≤ P) (hI : I ≠ ⊥) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ ∧ ¬ I ≤ ψ.ker}.Nonempty := by
  have hex : ∃ g ∈ I, g ≠ 1 := by
    by_contra h
    push Not at h
    exact hI (le_bot_iff.mp fun g hg ↦ Subgroup.mem_bot.mpr (h g hg))
  obtain ⟨g, hgI, hg1⟩ := hex
  have hgne : (⟨g, hIP hgI⟩ : P) ≠ 1 := fun h ↦ hg1 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity P O hgne
  refine ⟨hPH.extendChar φ χ, hPH.extendChar_comp_right φ χ, fun hle ↦ hφ ?_⟩
  have h1 := MonoidHom.mem_ker.mp (hle hgI)
  rw [← hPH.extendChar_coe_left φ χ ⟨g, hIP hgI⟩]
  exact h1

end CommSemiring

section CommRing

variable {O G : Type*} [CommRing O] [CommGroup G] {P H : Subgroup G}

section Domain

variable [IsDomain O] [Finite P] [HasEnoughRootsOfUnity O (Monoid.exponent P)]

/-- For complementary subgroups `P.IsComplement' H` with `P` finite and a domain `O` with enough
roots of unity of order `exponent P`, `α_{Ψ_χ}` and `MonoidAlgebra.componentProj hPH χ` have the
same kernel, even when `H` is infinite or `#H` is not a unit in `O`. -/
theorem ker_proj_eq_ker_componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    RingHom.ker (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ}) =
      RingHom.ker (MonoidAlgebra.componentProj hPH χ) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, proj_eq_zero_iff]
  constructor
  · intro hx
    refine TauCeti.eq_of_forall_charEval_eq fun φ ↦ ?_
    rw [map_zero, MonoidAlgebra.charEval_componentProj]
    exact hx (hPH.extendChar φ χ) (hPH.extendChar_comp_right φ χ)
  · intro hx ψ hψ
    rw [← hPH.extendChar_comp_self ψ, hψ, ← MonoidAlgebra.charEval_componentProj, hx, map_zero]

/-- **The `χ`-component character group ring is isomorphic to `O[P]`** (Dasgupta–Kakde, §2.2): for
complementary subgroups `P.IsComplement' H` with `P` finite and a domain `O` with enough roots of
unity of order `exponent P`, `R_{Ψ_χ} ≃ₐ[O] O[P]`. No finiteness or invertibility hypothesis on
`H` is required. -/
noncomputable def componentEquiv (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing ≃ₐ[O] MonoidAlgebra O P :=
  (Ideal.quotientKerAlgEquivOfSurjective (proj_surjective _)).symm.trans <|
    (Ideal.quotientEquivAlgOfEq O (ker_proj_eq_ker_componentProj hPH χ)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (MonoidAlgebra.componentProj_surjective hPH χ))

/-- `componentEquiv` sends `α_{Ψ_χ}(x)` to `MonoidAlgebra.componentProj hPH χ x`. -/
@[simp]
theorem componentEquiv_proj (hPH : P.IsComplement' H) (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    componentEquiv hPH χ (proj {ψ : G →* Oˣ | ψ.comp H.subtype = χ} x) =
      MonoidAlgebra.componentProj hPH χ x := by
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
  rw [AlgEquiv.apply_symm_apply, componentEquiv_proj,
    MonoidAlgebra.componentProj_mapDomainAlgHom_left]

/-- Evaluating `componentEquiv hPH χ y` at a character `φ : P →* Oˣ` reads off the
`hPH.extendChar φ χ`-coordinate of `y`. -/
@[simp]
theorem charEval_componentEquiv (hPH : P.IsComplement' H) (χ : H →* Oˣ) (φ : P →* Oˣ)
    (y : {ψ : G →* Oˣ | ψ.comp H.subtype = χ}.charGroupRing) :
    φ.charEval (componentEquiv hPH χ y) =
      (y : {ψ : G →* Oˣ | ψ.comp H.subtype = χ} → O)
        ⟨hPH.extendChar φ χ, hPH.extendChar_comp_right φ χ⟩ := by
  obtain ⟨x, rfl⟩ := proj_surjective _ y
  rw [componentEquiv_proj, MonoidAlgebra.charEval_componentProj, coe_proj_apply]

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
