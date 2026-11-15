/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.Index
public import TauCeti.LinearAlgebra.Trace.HattoriStallings
import TauCeti.Algebra.MonoidAlgebra.Basis
import TauCeti.Algebra.MonoidAlgebra.CosetBasis

/-!
# Group-ring Hattori–Stallings traces

For a group `G` and an arbitrary ring `Λ`, the identity-coefficient functional `x ↦ x.coeff 1` on
`Λ[G]` kills commutators modulo `[Λ, Λ]` and descends to
`MonoidAlgebra.cyclicCoeffOne Λ G : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (Stacks Project,
Section 64.15, Lemma 64.15.1). Composing with the Hattori–Stallings trace of a finite projective
left `Λ[G]`-module `P` defines `LinearMap.hattoriStallingsGroupTrace Λ G P` and, over a commutative
ring `A`, `LinearMap.projectiveGroupTrace A G P : End_{A[G]}(P) →+ A` without dividing by `|G|`.

## Main definitions and results

* `MonoidAlgebra.cyclicCoeffOne`: `Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (Lemma 64.15.1).
* `LinearMap.hattoriStallingsGroupTrace` and `LinearMap.projectiveGroupTrace`: group-ring traces
  over arbitrary `Λ` and commutative `A`.
* `LinearMap.hattoriStallingsGroupTrace_balancedExtension_mapDomainRingHom`: induction along an
  injective group homomorphism `p : H →* G` preserves the trace (Lemma 64.15.3).
* `LinearMap.hattoriStallingsGroupTrace_of_restrictSubgroup`: restriction to `H ≤ G` multiplies the
  trace by `H.index` (Lemma 64.15.2).
* `LinearMap.hattoriStallingsTrace_of_twistedSMul` and
  `LinearMap.hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace`:
  automorphism-twisted traces and forgetting the `G`-action (`Tr_Λ(u, P) = |G| • Tr_Λ^G(u, P)`).

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.1–64.15.3).
* P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
-/

public section

noncomputable section

namespace MonoidAlgebra

section CyclicCoeffOne

variable (Λ G : Type*) [Ring Λ] [Group G]

/-- Extracting the coefficient at `1 : G` as a `ℤ`-linear map `Λ[G] →ₗ[ℤ] Λ`. -/
def coeffOneIntLinearMap : MonoidAlgebra Λ G →ₗ[ℤ] Λ where
  toFun x := x.coeff 1
  map_add' x y := by simp
  map_smul' n x := by rw [RingHom.id_apply, coeff_smul, Finsupp.smul_apply]

@[simp]
theorem coeffOneIntLinearMap_apply (x : MonoidAlgebra Λ G) :
    coeffOneIntLinearMap Λ G x = x.coeff 1 :=
  (rfl)

variable {Λ G} in
/-- Modulo `[Λ, Λ]`, the identity coefficient of a product in `Λ[G]` is symmetric. -/
theorem mkQ_coeff_mul_one_comm (x y : MonoidAlgebra Λ G) :
    (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((x * y).coeff 1) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((y * x).coeff 1) := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    rw [add_mul, mul_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply,
      map_add, map_add, hx₁, hx₂]
  | single g a =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      rw [mul_add, add_mul, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply,
        map_add, map_add, hy₁, hy₂]
    | single h b =>
      simp only [single_mul_single]
      by_cases hgh : g * h = 1
      · have hhg : h * g = 1 := mul_eq_one_comm.1 hgh
        simp only [hgh, hhg, coeff_single, Finsupp.single_eq_same, Submodule.mkQ_apply,
          Submodule.Quotient.eq]
        exact TauCeti.mul_sub_mul_mem_commutatorSubmodule ℤ Λ a b
      · have hhg : h * g ≠ 1 := fun h ↦ hgh (mul_eq_one_comm.1 h)
        simp [coeff_single, Finsupp.single_eq_of_ne (Ne.symm hgh),
          Finsupp.single_eq_of_ne (Ne.symm hhg)]

variable {Λ G} in
/-- The identity coefficient of any element in `[Λ[G], Λ[G]]` belongs to `[Λ, Λ]`. -/
theorem coeff_one_mem_commutatorSubmodule {x : MonoidAlgebra Λ G}
    (hx : x ∈ TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G)) :
    x.coeff 1 ∈ TauCeti.commutatorSubmodule ℤ Λ := by
  have hle : TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G) ≤
      LinearMap.ker ((TauCeti.commutatorSubmodule ℤ Λ).mkQ.comp (coeffOneIntLinearMap Λ G)) :=
    (TauCeti.commutatorSubmodule_le_ker_iff _).2 fun a b ↦ mkQ_coeff_mul_one_comm a b
  simpa [Submodule.Quotient.mk_eq_zero] using LinearMap.mem_ker.1 (hle hx)

/-- **The identity-coefficient map on cyclic quotients**
`ε : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (Stacks Project, Section 64.15, Lemma 64.15.1). -/
def cyclicCoeffOne :
    TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ G) →ₗ[ℤ] TauCeti.cyclicQuotient ℤ Λ :=
  Submodule.mapQ (TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G))
    (TauCeti.commutatorSubmodule ℤ Λ) (coeffOneIntLinearMap Λ G)
    fun _ hx ↦ coeff_one_mem_commutatorSubmodule hx

@[simp]
theorem cyclicCoeffOne_mk (x : MonoidAlgebra Λ G) :
    cyclicCoeffOne Λ G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x.coeff 1) :=
  (rfl)

theorem cyclicCoeffOne_mkQ (x : MonoidAlgebra Λ G) :
    cyclicCoeffOne Λ G ((TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G)).mkQ x) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ (x.coeff 1) :=
  (rfl)

variable {Λ G}

/-- Naturality of `cyclicCoeffOne` in ring homomorphisms `φ : Λ →+* Λ'`. -/
@[simp]
theorem cyclicCoeffOne_mapRingHom {Λ' : Type*} [Ring Λ'] (φ : Λ →+* Λ')
    (c : TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ G)) :
    cyclicCoeffOne Λ' G (TauCeti.cyclicQuotientRingHomMap (mapRingHom G φ) c) =
      TauCeti.cyclicQuotientRingHomMap φ (cyclicCoeffOne Λ G c) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  simp

/-- Pushing forward along an injective monoid homomorphism preserves the identity coefficient. -/
theorem coeff_mapDomainRingHom_one {R H M : Type*} [Semiring R] [Monoid H] [Monoid M]
    {p : H →* M} (hp : Function.Injective p) (x : MonoidAlgebra R H) :
    (mapDomainRingHom R p x).coeff 1 = x.coeff 1 := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply, hx, hy]
  | single h r =>
    simp only [mapDomainRingHom_apply, mapDomain_single, coeff_single]
    by_cases hh : h = 1
    · subst hh; simp
    · have hp1 : (1 : M) ≠ p h := fun heq ↦ hh ((map_eq_one_iff p hp).1 heq.symm)
      simp [Finsupp.single_eq_of_ne hp1, Finsupp.single_eq_of_ne (Ne.symm hh)]

/-- Pushing forward along an injective group homomorphism `p : H →* G` preserves `cyclicCoeffOne`
(Stacks Project, Section 64.15, Lemma 64.15.3). -/
@[simp]
theorem cyclicCoeffOne_mapDomainRingHom {H : Type*} [Group H] {p : H →* G}
    (hp : Function.Injective p) (c : TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ H)) :
    cyclicCoeffOne Λ G (TauCeti.cyclicQuotientRingHomMap (mapDomainRingHom Λ p) c) =
      cyclicCoeffOne Λ H c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [TauCeti.cyclicQuotientRingHomMap_mk, cyclicCoeffOne_mk, cyclicCoeffOne_mk,
    coeff_mapDomainRingHom_one hp]

end CyclicCoeffOne

end MonoidAlgebra

namespace LinearMap

section NoncommRing

variable (Λ G P : Type*) [Ring Λ] [Group G] [AddCommGroup P] [Module (MonoidAlgebra Λ G) P]
  [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]

/-- **The group-ring Hattori–Stallings trace** `Tr_Λ^G(u, P) ∈ Λ / [Λ, Λ]` of a `Λ[G]`-linear
endomorphism `u` of a finite projective left `Λ[G]`-module `P` (Stacks Project, Section 64.15). -/
def hattoriStallingsGroupTrace :
    Module.End (MonoidAlgebra Λ G) P →+ TauCeti.cyclicQuotient ℤ Λ :=
  (MonoidAlgebra.cyclicCoeffOne Λ G).toAddMonoidHom.comp
    (hattoriStallingsTrace (MonoidAlgebra Λ G) P)

theorem hattoriStallingsGroupTrace_apply (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ G P u =
      MonoidAlgebra.cyclicCoeffOne Λ G (hattoriStallingsTrace (MonoidAlgebra Λ G) P u) :=
  (rfl)

variable {Λ G P}

/-- Cyclicity of `hattoriStallingsGroupTrace` across finite projective left `Λ[G]`-modules. -/
theorem hattoriStallingsGroupTrace_comp_comm {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : P →ₗ[MonoidAlgebra Λ G] Q) (v : Q →ₗ[MonoidAlgebra Λ G] P) :
    hattoriStallingsGroupTrace Λ G P (v ∘ₗ u) =
      hattoriStallingsGroupTrace Λ G Q (u ∘ₗ v) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_comp_comm]

/-- Conjugation invariance of `hattoriStallingsGroupTrace`. -/
@[simp]
theorem hattoriStallingsGroupTrace_conj {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : Module.End (MonoidAlgebra Λ G) P) (e : P ≃ₗ[MonoidAlgebra Λ G] Q) :
    hattoriStallingsGroupTrace Λ G Q (e.conjRingEquiv u) =
      hattoriStallingsGroupTrace Λ G P u := by
  simp [hattoriStallingsGroupTrace_apply]

/-- Additivity of `hattoriStallingsGroupTrace` on direct products. -/
@[simp]
theorem hattoriStallingsGroupTrace_prodMap {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : Module.End (MonoidAlgebra Λ G) P) (v : Module.End (MonoidAlgebra Λ G) Q) :
    hattoriStallingsGroupTrace Λ G (P × Q) (u.prodMap v) =
      hattoriStallingsGroupTrace Λ G P u + hattoriStallingsGroupTrace Λ G Q v := by
  simp [hattoriStallingsGroupTrace_apply]

/-- On the zero module `hattoriStallingsGroupTrace` vanishes. -/
@[simp]
theorem hattoriStallingsGroupTrace_eq_zero_of_subsingleton [Subsingleton P]
    (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ G P u = 0 := by
  simp [hattoriStallingsGroupTrace_apply]

/-- **Scalar extension along `φ : Λ →+* Λ'`.** -/
@[simp]
theorem hattoriStallingsGroupTrace_balancedExtension_mapRingHom {Λ' : Type*} [Ring Λ']
    (φ : Λ →+* Λ') (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ' G
        (TauCeti.BalancedExtension (MonoidAlgebra.mapRingHom G φ) P)
        (TauCeti.BalancedExtension.map (MonoidAlgebra.mapRingHom G φ) u) =
      TauCeti.cyclicQuotientRingHomMap φ (hattoriStallingsGroupTrace Λ G P u) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsTrace_balancedExtension_map,
    MonoidAlgebra.cyclicCoeffOne_mapRingHom, ← hattoriStallingsGroupTrace_apply]

end NoncommRing

section RegularAndInduction

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- On the regular left `Λ[G]`-module `Λ[G]`, `Tr_Λ^G(u) = [(u 1).coeff 1]`. -/
@[simp]
theorem hattoriStallingsGroupTrace_regular
    (u : Module.End (MonoidAlgebra Λ G) (MonoidAlgebra Λ G)) :
    hattoriStallingsGroupTrace Λ G (MonoidAlgebra Λ G) u =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((u 1).coeff 1) := by
  rw [hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_basis (Module.Basis.singleton Unit (MonoidAlgebra Λ G)),
    Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ]
  simp

/-- **Induction along an injective group homomorphism** (Stacks Project, Section 64.15,
Lemma 64.15.3): `Tr_Λ^G(Λ[G] ⊗_{Λ[H]} u) = Tr_Λ^H(u)`. -/
@[simp]
theorem hattoriStallingsGroupTrace_balancedExtension_mapDomainRingHom {H Q : Type*} [Group H]
    [AddCommGroup Q] [Module (MonoidAlgebra Λ H) Q] [Module.Finite (MonoidAlgebra Λ H) Q]
    [Module.Projective (MonoidAlgebra Λ H) Q] {p : H →* G} (hp : Function.Injective p)
    (u : Module.End (MonoidAlgebra Λ H) Q) :
    hattoriStallingsGroupTrace Λ G
        (TauCeti.BalancedExtension (MonoidAlgebra.mapDomainRingHom Λ p) Q)
        (TauCeti.BalancedExtension.map (MonoidAlgebra.mapDomainRingHom Λ p) u) =
      hattoriStallingsGroupTrace Λ H Q u := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsTrace_balancedExtension_map,
    MonoidAlgebra.cyclicCoeffOne_mapDomainRingHom hp, ← hattoriStallingsGroupTrace_apply]

end RegularAndInduction

end LinearMap

namespace LinearEquiv

/-- **Group-isomorphism transport of `hattoriStallingsGroupTrace`.** -/
theorem hattoriStallingsGroupTrace_eq_of_semilinear {Λ H G P P' : Type*} [Ring Λ] [Group H]
    [Group G] [AddCommGroup P] [Module (MonoidAlgebra Λ H) P] [AddCommGroup P']
    [Module (MonoidAlgebra Λ G) P'] [Module.Finite (MonoidAlgebra Λ H) P]
    [Module.Projective (MonoidAlgebra Λ H) P] [Module.Finite (MonoidAlgebra Λ G) P']
    [Module.Projective (MonoidAlgebra Λ G) P']
    {σ : MonoidAlgebra Λ H →+* MonoidAlgebra Λ G}
    {σ' : MonoidAlgebra Λ G →+* MonoidAlgebra Λ H}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e : H ≃* G)
    (hσ : σ = MonoidAlgebra.mapDomainRingHom Λ e.toMonoidHom) (j : P ≃ₛₗ[σ] P')
    {u : Module.End (MonoidAlgebra Λ H) P} {u' : Module.End (MonoidAlgebra Λ G) P'}
    (h : ∀ x, u' (j x) = j (u x)) :
    LinearMap.hattoriStallingsGroupTrace Λ G P' u' =
      LinearMap.hattoriStallingsGroupTrace Λ H P u := by
  rw [LinearMap.hattoriStallingsGroupTrace_apply, j.hattoriStallingsTrace_eq_map h, hσ,
    MonoidAlgebra.cyclicCoeffOne_mapDomainRingHom e.injective,
    ← LinearMap.hattoriStallingsGroupTrace_apply]

end LinearEquiv

namespace LinearMap

section Restriction

open MonoidAlgebra

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- Reindexing `∑ g : G, y.coeff ((σ g)⁻¹ * g)` over right cosets of
`Z = σ.toMonoidHom.eqLocus (.id G)` gives `|Z|` copies of the sum over `G ⧸ Z`. -/
private theorem sum_coeff_twisted_eq_card_nsmul (σ : G ≃* G) [Fintype G]
    [Fintype (G ⧸ (σ.toMonoidHom.eqLocus (.id G)).subtype.range)] (y : MonoidAlgebra Λ G) :
    ∑ g : G, y.coeff ((σ g)⁻¹ * g) =
      Nat.card (σ.toMonoidHom.eqLocus (.id G)) •
        ∑ q : G ⧸ (σ.toMonoidHom.eqLocus (.id G)).subtype.range,
          y.coeff ((σ q.out⁻¹)⁻¹ * q.out⁻¹) := by
  let Z := σ.toMonoidHom.eqLocus (.id G)
  let _ : Fintype Z := Fintype.ofFinite Z
  let eCoset : (G ⧸ Z.subtype.range) × Z ≃ G :=
    (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.inv Z).trans (MonoidHom.ofInjective Z.subtype_injective).toEquiv)).trans
        (Subgroup.groupEquivQuotientProdSubgroup.symm.trans (Equiv.inv G))
  have heCoset : ∀ (q : G ⧸ Z.subtype.range) (z : Z), eCoset (q, z) = (z : G) * q.out⁻¹ :=
    fun q z ↦ by
      simp [eCoset, Subgroup.groupEquivQuotientProdSubgroup_symm_apply, MonoidHom.ofInjective_apply]
  have hinv : ∀ (q : G ⧸ Z.subtype.range) (z : Z),
      (σ (eCoset (q, z)))⁻¹ * eCoset (q, z) = (σ q.out⁻¹)⁻¹ * q.out⁻¹ := fun q z ↦ by
    have hz : σ (z : G) = (z : G) := z.2
    rw [heCoset, map_mul, hz, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [← eCoset.sum_comp, Fintype.sum_prod_type_right]
  simp only [hinv, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Z]

variable {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra Λ G) P]

/-- If `G ⧸ H` is infinite, any finite projective `Λ[G]`-module that is finitely generated over
`Λ[H]` is trivial. -/
private theorem subsingleton_of_infinite_quotient (H : Subgroup G) [Infinite (G ⧸ H)]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ G) P] [Module (MonoidAlgebra Λ H) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p) :
    Subsingleton P := by
  classical
  obtain ⟨r, π, i, -, -, hπi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := MonoidAlgebra Λ H) (M := P)
  refine subsingleton_iff_forall_eq 0 |>.2 fun p ↦ ?_
  have hip : i p = 0 := by
    funext k; by_contra hne
    obtain ⟨g₁, hg₁⟩ := Finsupp.support_nonempty_iff.2 (coeff_eq_zero.not.2 hne)
    let S : Finset (G ⧸ H) :=
      s.biUnion fun m ↦ (i m k).coeff.support.image fun g₀ ↦ QuotientGroup.mk g₀⁻¹
    have hsupp : ∀ (x : P) (g : G), g ∈ (i x k).coeff.support →
        (QuotientGroup.mk g⁻¹ : G ⧸ H) ∈ S := fun x ↦ by
      have hx : x ∈ Submodule.span (MonoidAlgebra Λ H) (s : Set P) := hs.symm ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem m hm => exact fun g hg ↦ Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image_of_mem _ hg⟩
      | zero => simp
      | add x y _ _ hx hy =>
        intro g hg; rw [map_add, Pi.add_apply, coeff_add] at hg
        exact (Finset.mem_union.1 (Finsupp.support_add hg)).elim (hx g) (hy g)
      | smul c x _ hx =>
        induction c using induction_linear with
        | zero => simp
        | add c₁ c₂ hc₁ hc₂ =>
          intro g hg; rw [add_smul, map_add, Pi.add_apply, coeff_add] at hg
          exact (Finset.mem_union.1 (Finsupp.support_add hg)).elim (hc₁ g) (hc₂ g)
        | single h a =>
          intro g hg
          have himg : i (MonoidAlgebra.single h a • x) k =
              MonoidAlgebra.single (h : G) a * i x k := by
            rw [hP, map_smul]; simp [Pi.smul_apply, smul_eq_mul]
          rw [himg, Finsupp.mem_support_iff, coeff_single_mul_apply] at hg
          have hq : (QuotientGroup.mk g⁻¹ : G ⧸ H) = QuotientGroup.mk ((h : G)⁻¹ * g)⁻¹ :=
            QuotientGroup.eq.2 (by simp)
          exact hq ▸ hx _ (Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hg))
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
    let t : G := q.out⁻¹ * g₁⁻¹
    have ht : t * g₁ ∈ (i (MonoidAlgebra.single t (1 : Λ) • p) k).coeff.support := by
      rw [congrFun (map_smul i (MonoidAlgebra.single t (1 : Λ)) p) k, Pi.smul_apply, smul_eq_mul,
        Finsupp.mem_support_iff, coeff_single_mul_apply, inv_mul_cancel_left, one_mul]
      exact Finsupp.mem_support_iff.1 hg₁
    have hq' : (QuotientGroup.mk (t * g₁)⁻¹ : G ⧸ H) = q := by simp [t]
    exact hq (hq' ▸ hsupp _ _ ht)
  simpa [hip] using (LinearMap.congr_fun hπi p).symm

/-- If `G` is infinite, any finite projective `Λ[G]`-module finitely generated over `Λ` is
trivial. -/
private theorem subsingleton_of_infinite_group [Infinite G]
    (P : Type*) [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite Λ P] :
    Subsingleton P := by
  let H : Subgroup G := ⊥
  let _ : Module (MonoidAlgebra Λ H) P := Module.compHom P (mapDomainRingHom Λ H.subtype)
  have : Infinite (G ⧸ H) :=
    Infinite.of_injective (QuotientGroup.quotientBot (G := G)).symm
      (QuotientGroup.quotientBot (G := G)).symm.injective
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := P)
  let M : Submodule Λ P :=
    { Submodule.span (MonoidAlgebra Λ H) (s : Set P) with
      smul_mem' c x hx := by
        have hc : (MonoidAlgebra.single (1 : H) c : MonoidAlgebra Λ H) • x = c • x := by
          change mapDomainRingHom Λ H.subtype (MonoidAlgebra.single 1 c) • x = c • x
          have h1 : mapDomainRingHom Λ H.subtype (MonoidAlgebra.single 1 c) =
              c • (1 : MonoidAlgebra Λ G) := by simp [one_def]
          rw [h1, smul_assoc, one_smul]
        exact hc ▸ Submodule.smul_mem _ _ hx }
  have hle : (⊤ : Submodule Λ P) ≤ M := hs ▸ Submodule.span_le.2 Submodule.subset_span
  have : Module.Finite (MonoidAlgebra Λ H) P := ⟨⟨s, top_unique fun p hp ↦ hle hp⟩⟩
  exact subsingleton_of_infinite_quotient (Λ := Λ) H P (fun _ _ ↦ rfl)

/-- Evaluating `hattoriStallingsGroupTrace Λ H P u_H` on a `Λ[G]`-free retract `(π, i)` of `P` via
the coset basis `basisCosets Λ H.subtype`. -/
theorem hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract (H : Subgroup G)
    [Module (MonoidAlgebra Λ H) P] [Module.Finite (MonoidAlgebra Λ H) P]
    [Module.Projective (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    {r : ℕ} (π : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] P)
    (i : P →ₗ[MonoidAlgebra Λ G] Fin r → MonoidAlgebra Λ G) (hπi : π ∘ₗ i = .id)
    (u_H : Module.End (MonoidAlgebra Λ H) P) [Fintype (G ⧸ H.subtype.range)] :
    hattoriStallingsGroupTrace Λ H P u_H =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ H.subtype.range,
          (i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
            π (Pi.single k 1))) k).coeff q.out⁻¹) := by
  classical
  let φ := mapDomainRingHom Λ H.subtype
  let _ : Module (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) := φ.toModule
  let i_H : P →ₗ[MonoidAlgebra Λ H] Fin r → MonoidAlgebra Λ G :=
    { toFun := i, map_add' := map_add i,
      map_smul' := fun c p ↦ by rw [RingHom.id_apply, hP, map_smul]; ext k; rfl }
  let π_H : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ H] P :=
    { toFun := π, map_add' := map_add π,
      map_smul' := fun c v ↦ by
        have hv : c • v = φ c • v := rfl; rw [RingHom.id_apply, hv, map_smul, hP] }
  let bPi : Module.Basis ((_ : Fin r) × (G ⧸ H.subtype.range)) (MonoidAlgebra Λ H)
      (Fin r → MonoidAlgebra Λ G) :=
    Pi.basis fun _ ↦ TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective
  rw [hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_retract bPi i_H π_H
      (LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p),
    Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ]
  congr 1
  simp only [coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hb : bPi ⟨k, q⟩ =
      (MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
        Pi.single k (1 : MonoidAlgebra Λ G) := by
    ext j; by_cases hjk : j = k; · subst hjk; simp [bPi]
    · simp [bPi, Pi.single_eq_of_ne hjk]
  have hv : (i_H ∘ₗ u_H ∘ₗ π_H) (bPi ⟨k, q⟩) =
      i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
        π (Pi.single k 1))) := by
    have hπ : π_H (bPi ⟨k, q⟩) =
        (MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • π (Pi.single k 1) := by
      rw [hb]; exact map_smul π (MonoidAlgebra.single q.out⁻¹ 1) (Pi.single k 1)
    simp [i_H, hπ]
  rw [hv]; simp [bPi]

/-- **Subgroup restriction of the group-ring Hattori–Stallings trace** (Stacks Project,
Section 64.15, Lemma 64.15.2): `Tr_Λ^H(u, P) = H.index • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsGroupTrace_of_restrictSubgroup (H : Subgroup G)
    [Module (MonoidAlgebra Λ H) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ H) P]
    [Module.Projective (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (u : Module.End (MonoidAlgebra Λ G) P) (u_H : Module.End (MonoidAlgebra Λ H) P)
    (hu : ∀ p, u_H p = u p) :
    hattoriStallingsGroupTrace Λ H P u_H =
      H.index • hattoriStallingsGroupTrace Λ G P u := by
  rcases finite_or_infinite (G ⧸ H) with _ | _
  · classical
    have : Finite (G ⧸ H.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    let _ : Fintype (G ⧸ H.subtype.range) := Fintype.ofFinite _
    obtain ⟨r, π, i, -, -, hπi⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
    rw [hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract H hP π i hπi u_H,
      hattoriStallingsGroupTrace_apply,
      hattoriStallingsTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra Λ G) (Fin r)) i π hπi,
      Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ, ← map_nsmul]
    have hcard : Fintype.card (G ⧸ H.subtype.range) = H.index := by
      rw [← Nat.card_eq_fintype_card, Subgroup.range_subtype, Subgroup.index]
    rw [← hcard]
    congr 1
    simp only [coeff_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hq : ∀ q : G ⧸ H.subtype.range,
        (i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
          π (Pi.single k 1))) k).coeff q.out⁻¹ =
          (i (u (π (Pi.single k 1))) k).coeff 1 := fun q ↦ by
      have himg : i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
          π (Pi.single k 1))) k =
          MonoidAlgebra.single q.out⁻¹ (1 : Λ) * i (u (π (Pi.single k 1))) k := by
        rw [hu, map_smul u]; exact congrFun (map_smul i _ _) k
      simp [himg]
    simp [hq]
  · have := subsingleton_of_infinite_quotient H P hP
    simp

/-- An endomorphism `φ : P →ₗ[Λ] P` satisfying `φ (single g 1 • p) = single (σ g) 1 • φ p` restricts
to a `Λ[H]`-linear endomorphism on any subgroup `H ≤ σ.toMonoidHom.eqLocus (.id G)`. -/
def restrictFixedSubgroup [Module Λ P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    {σ : G ≃* G} {H : Subgroup G} (hle : H ≤ σ.toMonoidHom.eqLocus (.id G))
    [Module (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (φ : Module.End Λ P)
    (hφ : ∀ (g : G) (p : P), φ (MonoidAlgebra.single g (1 : Λ) • p) =
      MonoidAlgebra.single (σ g) (1 : Λ) • φ p) :
    Module.End (MonoidAlgebra Λ H) P where
  toFun := φ
  map_add' := map_add φ
  map_smul' r p := by
    rw [RingHom.id_apply, hP, hP]
    induction r using induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, add_smul, map_add, add_smul, hx, hy]
    | single h c =>
      simp only [mapDomainRingHom_apply, mapDomain_single]
      have hh : σ (H.subtype h) = H.subtype h := hle h.2
      have hsmul : ∀ (g : G) (q : P),
          MonoidAlgebra.single g c • q = c • (MonoidAlgebra.single g (1 : Λ) • q) := fun g q ↦ by
        have hc : (MonoidAlgebra.single g c : MonoidAlgebra Λ G) =
            c • MonoidAlgebra.single g (1 : Λ) := by rw [smul_single, smul_eq_mul, mul_one]
        rw [hc, smul_assoc]
      rw [hsmul, map_smul, hφ, hh, ← hsmul]

@[simp]
theorem restrictFixedSubgroup_apply [Module Λ P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    {σ : G ≃* G} {H : Subgroup G} (hle : H ≤ σ.toMonoidHom.eqLocus (.id G))
    [Module (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (φ : Module.End Λ P)
    (hφ : ∀ (g : G) (p : P), φ (MonoidAlgebra.single g (1 : Λ) • p) =
      MonoidAlgebra.single (σ g) (1 : Λ) • φ p) (p : P) :
    restrictFixedSubgroup hle hP φ hφ p = φ p :=
  (rfl)

/-- **Trace of an automorphism-twisted endomorphism of a finite projective `Λ[G]`-module.** If
`σ : G ≃* G`, `Z = σ.toMonoidHom.eqLocus (.id G)`, and `φ : P →ₗ[Λ] P` satisfies
`φ (single g 1 • p) = single (σ g) 1 • φ p`, then `Tr_Λ(φ, P) = |Z| • Tr_Λ^Z(φ, P)`. -/
theorem hattoriStallingsTrace_of_twistedSMul {σ : G ≃* G} {Z : Subgroup G}
    (hZ : Z = σ.toMonoidHom.eqLocus (.id G)) [Module Λ P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite Λ P] [Module.Projective Λ P]
    [Module (MonoidAlgebra Λ Z) P] [Module.Finite (MonoidAlgebra Λ Z) P]
    [Module.Projective (MonoidAlgebra Λ Z) P]
    (hP : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = mapDomainRingHom Λ Z.subtype r • p)
    (φ : Module.End Λ P) (φ_Z : Module.End (MonoidAlgebra Λ Z) P)
    (hφ : ∀ (g : G) (p : P), φ (MonoidAlgebra.single g (1 : Λ) • p) =
      MonoidAlgebra.single (σ g) (1 : Λ) • φ p)
    (hφZ : ∀ p, φ_Z p = φ p) :
    hattoriStallingsTrace Λ P φ =
      Nat.card Z • hattoriStallingsGroupTrace Λ Z P φ_Z := by
  rcases finite_or_infinite G with _ | _
  · subst hZ; classical
    let Z := σ.toMonoidHom.eqLocus (.id G)
    let _ : Fintype G := Fintype.ofFinite G
    have : Finite (G ⧸ Z.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    let _ : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
    obtain ⟨r, π, i, -, -, hπi⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
    let i_Λ := i.restrictScalars Λ; let π_Λ := π.restrictScalars Λ
    let bΛ : Module.Basis ((_ : Fin r) × G) Λ (Fin r → MonoidAlgebra Λ G) :=
      Pi.basis fun _ ↦ MonoidAlgebra.basis G Λ
    rw [hattoriStallingsTrace_eq_of_retract bΛ i_Λ π_Λ
        (LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p),
      Module.Basis.hattoriStallingsTrace_apply,
      hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract Z hP π i hπi φ_Z, ← map_nsmul]
    congr 1
    simp only [Fintype.sum_sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let yk := i (φ (π (Pi.single k 1))) k
    have hLHS : ∀ g : G,
        (bΛ.repr ((i_Λ ∘ₗ φ ∘ₗ π_Λ) (bΛ ⟨k, g⟩))) ⟨k, g⟩ = yk.coeff ((σ g)⁻¹ * g) := fun g ↦ by
      have hb : bΛ ⟨k, g⟩ = MonoidAlgebra.single g (1 : Λ) • Pi.single k 1 := by
        ext j; by_cases hjk : j = k; · subst hjk; simp [bΛ]
        · simp [bΛ, Pi.single_eq_of_ne hjk]
      have himg : ((i_Λ ∘ₗ φ ∘ₗ π_Λ) (bΛ ⟨k, g⟩)) k =
          MonoidAlgebra.single (σ g) (1 : Λ) * yk := by
        rw [hb, comp_apply, comp_apply]
        simp only [i_Λ, π_Λ, restrictScalars_apply]
        rw [map_smul, hφ]
        exact congrFun (map_smul i (MonoidAlgebra.single (σ g) (1 : Λ)) _) k
      have hrepr : ∀ v, (bΛ.repr v) ⟨k, g⟩ = (v k).coeff g := fun v ↦ by simp [bΛ]
      rw [hrepr, himg, coeff_single_mul_apply, one_mul]
    have hRHS : ∀ q : G ⧸ Z.subtype.range,
        (i (φ_Z ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
          π (Pi.single k 1))) k).coeff q.out⁻¹ =
          yk.coeff ((σ q.out⁻¹)⁻¹ * q.out⁻¹) := fun q ↦ by
      have himg : i (φ_Z ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
          π (Pi.single k 1))) k = MonoidAlgebra.single (σ q.out⁻¹) (1 : Λ) * yk := by
        rw [hφZ, hφ]; exact congrFun (map_smul i _ _) k
      rw [himg, coeff_single_mul_apply, one_mul]
    simp only [hLHS, hRHS, ← Finset.smul_sum]
    exact sum_coeff_twisted_eq_card_nsmul σ yk
  · have := subsingleton_of_infinite_group (Λ := Λ) (G := G) P
    simp

/-- **Forgetting a group action multiplies the group-ring trace by `|G|`** (Stacks Project,
Lemma 64.15.2 for the trivial subgroup): `Tr_Λ(u, P) = Nat.card G • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace
    [Module Λ P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Module.Finite Λ P] [Module.Projective Λ P] (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsTrace Λ P (u.restrictScalars Λ) =
      Nat.card G • hattoriStallingsGroupTrace Λ G P u := by
  rcases finite_or_infinite G with _ | _
  · classical
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨r, π, i, -, -, hπi⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
    let bG : Module.Basis (Fin r) (MonoidAlgebra Λ G) (Fin r → MonoidAlgebra Λ G) :=
      Pi.basisFun (MonoidAlgebra Λ G) (Fin r)
    let bΛ : Module.Basis ((_ : Fin r) × G) Λ (Fin r → MonoidAlgebra Λ G) :=
      Pi.basis fun _ ↦ MonoidAlgebra.basis G Λ
    have hret : (π.restrictScalars Λ).comp (i.restrictScalars Λ) = .id :=
      LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p
    rw [hattoriStallingsTrace_eq_of_retract bΛ (i.restrictScalars Λ) (π.restrictScalars Λ) hret,
      Module.Basis.hattoriStallingsTrace_apply, hattoriStallingsGroupTrace_apply,
      hattoriStallingsTrace_eq_of_retract bG i π hπi, Module.Basis.hattoriStallingsTrace_apply,
      MonoidAlgebra.cyclicCoeffOne_mkQ, ← map_nsmul]
    congr 1
    simp only [Fintype.sum_sigma, coeff_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hterm : ∀ g : G,
        (bΛ.repr ((i.restrictScalars Λ ∘ₗ u.restrictScalars Λ ∘ₗ π.restrictScalars Λ)
          (bΛ ⟨k, g⟩))) ⟨k, g⟩ = ((bG.repr ((i ∘ₗ u ∘ₗ π) (bG k))) k).coeff 1 := fun g ↦ by
      have hb : bΛ ⟨k, g⟩ = MonoidAlgebra.single g (1 : Λ) • Pi.single k 1 := by
        ext j; by_cases hjk : j = k; · subst hjk; simp [bΛ]
        · simp [bΛ, Pi.single_eq_of_ne hjk]
      have himg : (i (u (π (bΛ ⟨k, g⟩)))) k =
          MonoidAlgebra.single g (1 : Λ) * (i (u (π (Pi.single k 1)))) k := by
        rw [hb, map_smul, map_smul]
        exact congrFun (map_smul i (MonoidAlgebra.single g (1 : Λ)) _) k
      have hrepr : ∀ v, (bΛ.repr v) ⟨k, g⟩ = (v k).coeff g := fun v ↦ by simp [bΛ]
      change (bΛ.repr (i (u (π (bΛ ⟨k, g⟩))))) ⟨k, g⟩ = _
      rw [hrepr, himg, coeff_single_mul_apply, inv_mul_cancel, one_mul]
      simp [bG]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  · have := subsingleton_of_infinite_group (Λ := Λ) (G := G) P
    simp

end Restriction

section CommRing

variable (A G P : Type*) [CommRing A] [Group G] [AddCommGroup P] [Module (MonoidAlgebra A G) P]
  [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]

/-- **The scalar-valued group-ring trace over a commutative ring** `Tr_A^G(u, P) ∈ A`. -/
def projectiveGroupTrace : Module.End (MonoidAlgebra A G) P →+ A :=
  (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom.comp
    (hattoriStallingsGroupTrace A G P)

variable {A G P}

theorem projectiveGroupTrace_apply (u : Module.End (MonoidAlgebra A G) P) :
    projectiveGroupTrace A G P u =
      TauCeti.cyclicQuotientEquivOfCommRing ℤ A (hattoriStallingsGroupTrace A G P u) :=
  (rfl)

theorem hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace
    (u : Module.End (MonoidAlgebra A G) P) :
    hattoriStallingsGroupTrace A G P u =
      (TauCeti.commutatorSubmodule ℤ A).mkQ (projectiveGroupTrace A G P u) := by
  rw [projectiveGroupTrace_apply, ← TauCeti.cyclicQuotientEquivOfCommRing_symm_apply]
  exact ((TauCeti.cyclicQuotientEquivOfCommRing ℤ A).symm_apply_apply
    (hattoriStallingsGroupTrace A G P u)).symm

/-- Scalar extension of `projectiveGroupTrace` along `φ : A →+* B`. -/
@[simp]
theorem projectiveGroupTrace_balancedExtension_mapRingHom {B : Type*} [CommRing B] (φ : A →+* B)
    (u : Module.End (MonoidAlgebra A G) P) :
    projectiveGroupTrace B G
        (TauCeti.BalancedExtension (MonoidAlgebra.mapRingHom G φ) P)
        (TauCeti.BalancedExtension.map (MonoidAlgebra.mapRingHom G φ) u) =
      φ (projectiveGroupTrace A G P u) := by
  rw [projectiveGroupTrace_apply, hattoriStallingsGroupTrace_balancedExtension_mapRingHom,
    hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace, TauCeti.cyclicQuotientRingHomMap_mkQ,
    TauCeti.cyclicQuotientEquivOfCommRing_mkQ]

/-- Induction along an injective group homomorphism preserves `projectiveGroupTrace`. -/
@[simp]
theorem projectiveGroupTrace_balancedExtension_mapDomainRingHom {H Q : Type*} [Group H]
    [AddCommGroup Q] [Module (MonoidAlgebra A H) Q] [Module.Finite (MonoidAlgebra A H) Q]
    [Module.Projective (MonoidAlgebra A H) Q] {p : H →* G} (hp : Function.Injective p)
    (u : Module.End (MonoidAlgebra A H) Q) :
    projectiveGroupTrace A G
        (TauCeti.BalancedExtension (MonoidAlgebra.mapDomainRingHom A p) Q)
        (TauCeti.BalancedExtension.map (MonoidAlgebra.mapDomainRingHom A p) u) =
      projectiveGroupTrace A H Q u := by
  simp [projectiveGroupTrace_apply, hp]

/-- Subgroup restriction multiplies `projectiveGroupTrace` by `[G : H]`. -/
theorem projectiveGroupTrace_of_restrictSubgroup (H : Subgroup G)
    [Module (MonoidAlgebra A H) P] [Module.Finite (MonoidAlgebra A H) P]
    [Module.Projective (MonoidAlgebra A H) P]
    (hP : ∀ (r : MonoidAlgebra A H) (p : P),
      r • p = MonoidAlgebra.mapDomainRingHom A H.subtype r • p)
    (u : Module.End (MonoidAlgebra A G) P) (u_H : Module.End (MonoidAlgebra A H) P)
    (hu : ∀ p, u_H p = u p) :
    projectiveGroupTrace A H P u_H = H.index * projectiveGroupTrace A G P u := by
  have h := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom
    (hattoriStallingsGroupTrace_of_restrictSubgroup H hP u u_H hu)
  simpa [hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace, map_nsmul, nsmul_eq_mul] using h

/-- Over a commutative ring `A`, `Tr_A(u, P) = |G| * Tr_A^G(u, P)`. -/
theorem projectiveTrace_restrictScalars_eq_card_mul_projectiveGroupTrace
    [Module A P] [IsScalarTower A (MonoidAlgebra A G) P] [Module.Finite A P] [Module.Projective A P]
    (u : Module.End (MonoidAlgebra A G) P) :
    projectiveTrace A P (u.restrictScalars A) =
      (Nat.card G : A) * projectiveGroupTrace A G P u := by
  have h := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom
    (hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace u)
  simpa [hattoriStallingsTrace_eq_projectiveTrace,
    hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace, map_nsmul, nsmul_eq_mul] using h

end CommRing

end LinearMap

end
