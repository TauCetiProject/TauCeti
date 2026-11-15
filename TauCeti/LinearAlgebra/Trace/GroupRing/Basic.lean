/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Algebra.MonoidAlgebra.Basis
public import TauCeti.Algebra.MonoidAlgebra.CosetBasis
public import TauCeti.LinearAlgebra.Trace.HattoriStallings
import TauCeti.Algebra.Module.Projective.Trans

/-!
# Group-ring Hattori–Stallings traces

For a group `G` and an arbitrary ring `Λ`, the identity-coefficient functional `x ↦ x.coeff 1` on
`Λ[G]` kills commutators modulo `[Λ, Λ]`: for monomials `single g a` and `single h b`, the product
`g * h` is `1` if and only if `h * g = 1`, in which case the difference of identity coefficients is
the commutator `a * b - b * a ∈ [Λ, Λ]`. Consequently `coeff 1` descends to an additive map
`MonoidAlgebra.cyclicCoeffOne Λ G : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (Stacks Project,
Section 64.15, Lemma 64.15.1).

Composing `MonoidAlgebra.cyclicCoeffOne Λ G` with the Hattori–Stallings trace of a finite projective
left `Λ[G]`-module `P` defines the **group-ring Hattori–Stallings trace**
`LinearMap.hattoriStallingsGroupTrace Λ G P : End_{Λ[G]}(P) →+ Λ / [Λ, Λ]`, together with its
scalar-valued specialization `LinearMap.projectiveGroupTrace A G P : End_{A[G]}(P) →+ A` when `A`
is commutative (even when `G` is nonabelian, so `A[G]` itself is noncommutative). No division by
`|G|` is involved, so all identities remain valid when `|G| = 0` in `Λ`.

## Main definitions

* `MonoidAlgebra.cyclicCoeffOne`: the identity-coefficient map
  `Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]`.
* `LinearMap.hattoriStallingsGroupTrace`: the group-ring Hattori–Stallings trace
  `Tr_Λ^G(u, P) ∈ Λ / [Λ, Λ]` of a `Λ[G]`-linear endomorphism `u` of a finite projective left
  `Λ[G]`-module `P`.
* `LinearMap.projectiveGroupTrace`: for commutative `A`, the `A`-valued group-ring trace
  `Tr_A^G(u, P) ∈ A`.

## Main results

* `MonoidAlgebra.cyclicCoeffOne_mapDomainRingHom`: an injective group homomorphism `p : H →* G`
  preserves `cyclicCoeffOne`.
* `LinearMap.hattoriStallingsGroupTrace_balancedExtension_mapRingHom`: compatibility with extension
  of scalars along any ring homomorphism `Λ →+* Λ'`.
* `LinearMap.hattoriStallingsGroupTrace_balancedExtension_mapDomainRingHom`: **induction** along an
  injective group homomorphism `p : H →* G` preserves the group-ring trace
  `Tr_Λ^G(Λ[G] ⊗_{Λ[H]} u) = Tr_Λ^H(u)` (Stacks Project, Section 64.15, Lemma 64.15.3).
* `LinearMap.hattoriStallingsGroupTrace_of_restrictSubgroup`: **restriction** to a finite-index
  subgroup `H ≤ G` multiplies the group-ring trace by `[G : H]`:
  `Tr_Λ^H(u, P) = [G : H] • Tr_Λ^G(u, P)` (Stacks Project, Section 64.15, Lemma 64.15.2).
* `LinearMap.hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace`: for
  finite `G`, forgetting the `G`-action multiplies the group-ring trace by `|G|`:
  `Tr_Λ(u, P) = |G| • Tr_Λ^G(u, P)`.

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.1–64.15.3).
* P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
* A. Grothendieck et al., *Cohomologie ℓ-adique et fonctions L* (SGA 5), Exposé III.
* H. Bass, *Algebraic K-theory*, Chapter II, Section 4.
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
/-- Modulo `[Λ, Λ]`, the identity coefficient of a product in a group ring `Λ[G]` is symmetric in
the two factors. -/
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
        have h1 : (1 : G) ≠ g * h := Ne.symm hgh
        have h2 : (1 : G) ≠ h * g := Ne.symm hhg
        simp [coeff_single, Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2]

variable {Λ G} in
/-- The identity coefficient of any element in the commutator submodule `[Λ[G], Λ[G]]` belongs to
the commutator submodule `[Λ, Λ]`. -/
theorem coeff_one_mem_commutatorSubmodule {x : MonoidAlgebra Λ G}
    (hx : x ∈ TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G)) :
    x.coeff 1 ∈ TauCeti.commutatorSubmodule ℤ Λ := by
  have hle : TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G) ≤
      LinearMap.ker ((TauCeti.commutatorSubmodule ℤ Λ).mkQ.comp (coeffOneIntLinearMap Λ G)) :=
    (TauCeti.commutatorSubmodule_le_ker_iff _).2 fun a b ↦ mkQ_coeff_mul_one_comm a b
  have hker := LinearMap.mem_ker.1 (hle hx)
  simpa [Submodule.Quotient.mk_eq_zero] using hker

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
    · subst hh
      simp
    · have hp1 : (1 : M) ≠ p h := fun heq ↦ hh ((map_eq_one_iff p hp).1 heq.symm)
      have hh1 : (1 : H) ≠ h := Ne.symm hh
      simp [Finsupp.single_eq_of_ne hp1, Finsupp.single_eq_of_ne hh1]

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

/-- Group isomorphisms preserve `cyclicCoeffOne`. -/
@[simp]
theorem cyclicCoeffOne_mapDomainRingEquiv {H : Type*} [Group H] (e : H ≃* G)
    (c : TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ H)) :
    cyclicCoeffOne Λ G
        (TauCeti.cyclicQuotientRingHomMap
          (mapDomainRingEquiv Λ e : MonoidAlgebra Λ H →+* MonoidAlgebra Λ G) c) =
      cyclicCoeffOne Λ H c := by
  rw [← RingEquiv.toRingHom_eq_coe, toRingHom_mapDomainRingEquiv,
    cyclicCoeffOne_mapDomainRingHom e.injective]

end CyclicCoeffOne

/-- A finite projective left `Λ[G]`-module over a finite group `G` is finite and projective over
`Λ`. -/
theorem finite_projective_of_group {Λ G : Type*} [Semiring Λ] [Group G] [Finite G]
    (P : Type*) [AddCommMonoid P] [Module Λ P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] :
    Module.Finite Λ P ∧ Module.Projective Λ P := by
  have : Module.Free Λ (MonoidAlgebra Λ G) := .of_basis (MonoidAlgebra.basis G Λ)
  exact ⟨.trans (MonoidAlgebra Λ G) P, .trans (MonoidAlgebra Λ G) P⟩

end MonoidAlgebra

namespace LinearMap

section NoncommRing

variable (Λ G P : Type*) [Ring Λ] [Group G] [AddCommGroup P] [Module (MonoidAlgebra Λ G) P]

/-- **The group-ring Hattori–Stallings trace** `Tr_Λ^G(u, P) ∈ Λ / [Λ, Λ]` of a `Λ[G]`-linear
endomorphism `u` of a finite projective left `Λ[G]`-module `P`, defined as the identity coefficient
of its universal Hattori–Stallings trace (Stacks Project, Section 64.15). -/
def hattoriStallingsGroupTrace [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] :
    Module.End (MonoidAlgebra Λ G) P →+ TauCeti.cyclicQuotient ℤ Λ :=
  (MonoidAlgebra.cyclicCoeffOne Λ G).toAddMonoidHom.comp
    (hattoriStallingsTrace (MonoidAlgebra Λ G) P)

theorem hattoriStallingsGroupTrace_apply [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ G P u =
      MonoidAlgebra.cyclicCoeffOne Λ G (hattoriStallingsTrace (MonoidAlgebra Λ G) P u) :=
  (rfl)

variable {Λ G P}

/-- Cyclicity of the group-ring Hattori–Stallings trace across finite projective left
`Λ[G]`-modules. -/
theorem hattoriStallingsGroupTrace_comp_comm {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : P →ₗ[MonoidAlgebra Λ G] Q) (v : Q →ₗ[MonoidAlgebra Λ G] P) :
    hattoriStallingsGroupTrace Λ G P (v ∘ₗ u) =
      hattoriStallingsGroupTrace Λ G Q (u ∘ₗ v) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_comp_comm]

/-- Conjugation invariance of the group-ring Hattori–Stallings trace. -/
@[simp]
theorem hattoriStallingsGroupTrace_conj {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : Module.End (MonoidAlgebra Λ G) P) (e : P ≃ₗ[MonoidAlgebra Λ G] Q) :
    hattoriStallingsGroupTrace Λ G Q (e.conjRingEquiv u) =
      hattoriStallingsGroupTrace Λ G P u := by
  simp [hattoriStallingsGroupTrace_apply]

/-- Additivity of the group-ring Hattori–Stallings trace on direct products. -/
@[simp]
theorem hattoriStallingsGroupTrace_prodMap {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q]
    (u : Module.End (MonoidAlgebra Λ G) P) (v : Module.End (MonoidAlgebra Λ G) Q) :
    hattoriStallingsGroupTrace Λ G (P × Q) (u.prodMap v) =
      hattoriStallingsGroupTrace Λ G P u + hattoriStallingsGroupTrace Λ G Q v := by
  simp [hattoriStallingsGroupTrace_apply]

/-- Split-exact additivity of the group-ring Hattori–Stallings trace from an identity
decomposition. -/
theorem hattoriStallingsGroupTrace_eq_add_of_id_decomposition
    {M N : Type*} [AddCommGroup M] [Module (MonoidAlgebra Λ G) M]
    [AddCommGroup N] [Module (MonoidAlgebra Λ G) N]
    [Module.Finite (MonoidAlgebra Λ G) M] [Module.Projective (MonoidAlgebra Λ G) M]
    [Module.Finite (MonoidAlgebra Λ G) N] [Module.Projective (MonoidAlgebra Λ G) N]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (i : M →ₗ[MonoidAlgebra Λ G] P) (r : P →ₗ[MonoidAlgebra Λ G] M)
    (j : N →ₗ[MonoidAlgebra Λ G] P) (s : P →ₗ[MonoidAlgebra Λ G] N)
    (h : i ∘ₗ r + j ∘ₗ s = .id) (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ G P u =
      hattoriStallingsGroupTrace Λ G M (r ∘ₗ u ∘ₗ i) +
        hattoriStallingsGroupTrace Λ G N (s ∘ₗ u ∘ₗ j) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsTrace_eq_add_of_id_decomposition i r j s h,
    map_add, ← hattoriStallingsGroupTrace_apply, ← hattoriStallingsGroupTrace_apply]

/-- On the zero module the group-ring Hattori–Stallings trace vanishes. -/
@[simp]
theorem hattoriStallingsGroupTrace_eq_zero_of_subsingleton
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Subsingleton P] (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ G P u = 0 := by
  simp [hattoriStallingsGroupTrace_apply]

/-- On the regular left `Λ[G]`-module `Λ[G]`, the group-ring trace of a `Λ[G]`-linear endomorphism
`u` is the cyclic class of `(u 1).coeff 1`. -/
@[simp]
theorem hattoriStallingsGroupTrace_regular
    (u : Module.End (MonoidAlgebra Λ G) (MonoidAlgebra Λ G)) :
    hattoriStallingsGroupTrace Λ G (MonoidAlgebra Λ G) u =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((u 1).coeff 1) := by
  rw [hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_basis (Module.Basis.singleton Unit (MonoidAlgebra Λ G)),
    Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ]
  simp

/-- **Scalar extension along `φ : Λ →+* Λ'`.** Extending coefficients of `Λ[G]` along a ring
homomorphism `φ` commutes with `hattoriStallingsGroupTrace`. -/
@[simp]
theorem hattoriStallingsGroupTrace_balancedExtension_mapRingHom {Λ' : Type*} [Ring Λ']
    (φ : Λ →+* Λ') [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsGroupTrace Λ' G
        (TauCeti.BalancedExtension (MonoidAlgebra.mapRingHom G φ) P)
        (TauCeti.BalancedExtension.map (MonoidAlgebra.mapRingHom G φ) u) =
      TauCeti.cyclicQuotientRingHomMap φ (hattoriStallingsGroupTrace Λ G P u) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsTrace_balancedExtension_map,
    MonoidAlgebra.cyclicCoeffOne_mapRingHom, ← hattoriStallingsGroupTrace_apply]

/-- **Induction along an injective group homomorphism** (Stacks Project, Section 64.15,
Lemma 64.15.3). For an injective homomorphism `p : H →* G` and an endomorphism `u` of a finite
projective left `Λ[H]`-module `Q`, the induced endomorphism on `Λ[G] ⊗_{Λ[H]} Q` has the same
group-ring trace: `Tr_Λ^G(Λ[G] ⊗_{Λ[H]} u) = Tr_Λ^H(u)`. -/
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

end NoncommRing

end LinearMap

namespace LinearEquiv

/-- **Group-isomorphism transport of `hattoriStallingsGroupTrace`.** If `e : H ≃* G` and
`j : P ≃ₛₗ[σ] P'` is semilinear along `σ = mapDomainRingHom Λ e.toMonoidHom` and intertwines `u`
and `u'`, then `u` and `u'` have the same group-ring Hattori–Stallings trace in `Λ / [Λ, Λ]`. -/
theorem hattoriStallingsGroupTrace_eq_of_semilinear {Λ H G P P' : Type*} [Ring Λ] [Group H]
    [Group G] [AddCommGroup P] [Module (MonoidAlgebra Λ H) P] [AddCommGroup P']
    [Module (MonoidAlgebra Λ G) P'] [Module.Finite (MonoidAlgebra Λ H) P]
    [Module.Projective (MonoidAlgebra Λ H) P] [Module.Finite (MonoidAlgebra Λ G) P']
    [Module.Projective (MonoidAlgebra Λ G) P']
    {σ : MonoidAlgebra Λ H →+* MonoidAlgebra Λ G}
    {σ' : MonoidAlgebra Λ G →+* MonoidAlgebra Λ H}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e : H ≃* G)
    (hσ : σ = MonoidAlgebra.mapDomainRingHom Λ e.toMonoidHom)
    (j : P ≃ₛₗ[σ] P')
    {u : Module.End (MonoidAlgebra Λ H) P} {u' : Module.End (MonoidAlgebra Λ G) P'}
    (h : ∀ x, u' (j x) = j (u x)) :
    LinearMap.hattoriStallingsGroupTrace Λ G P' u' =
      LinearMap.hattoriStallingsGroupTrace Λ H P u := by
  rw [LinearMap.hattoriStallingsGroupTrace_apply, j.hattoriStallingsTrace_eq_map h, hσ,
    MonoidAlgebra.cyclicCoeffOne_mapDomainRingHom e.injective,
    ← LinearMap.hattoriStallingsGroupTrace_apply]

end LinearEquiv

namespace MonoidAlgebra

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- For a subgroup `H ≤ G` and coset classes `q, q' : G ⧸ H.subtype.range`, the coefficient at
`q.out⁻¹` of `mapDomain H.subtype z * single q'.out⁻¹ 1` is `z.coeff 1` when `q' = q` and `0`
otherwise. -/
private theorem coeff_mapDomain_subtype_mul_single_out_inv {H : Subgroup G}
    [DecidableEq (G ⧸ H.subtype.range)] (q q' : G ⧸ H.subtype.range) (z : MonoidAlgebra Λ H) :
    (mapDomain H.subtype z * single q'.out⁻¹ (1 : Λ)).coeff q.out⁻¹ =
      if q' = q then z.coeff 1 else 0 := by
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
    simp only [mapDomain_add, add_mul, coeff_add, Finsupp.add_apply, hz₁, hz₂]
    split_ifs <;> simp
  | single h c =>
    simp only [mapDomain_single, single_mul_single, mul_one, coeff_single]
    by_cases hqq : q' = q
    · subst hqq
      simp only [↓reduceIte]
      by_cases hh : h = 1
      · subst hh
        simp
      · have hne : q'.out⁻¹ ≠ (h : G) * q'.out⁻¹ :=
          fun heq ↦ hh <| Subtype.ext <|
            mul_right_cancel (heq.symm.trans (one_mul q'.out⁻¹).symm)
        have hh1 : (1 : H) ≠ h := Ne.symm hh
        rw [Subgroup.coe_subtype, Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hh1]
    · simp only [hqq, ↓reduceIte]
      have hne : q.out⁻¹ ≠ H.subtype h * q'.out⁻¹ := by
        intro heq
        apply hqq
        have hmem : (q'.out)⁻¹ * q.out ∈ H.subtype.range := by
          refine ⟨h⁻¹, ?_⟩
          calc
            H.subtype h⁻¹ = H.subtype h⁻¹ * (q.out⁻¹ * q.out) := by simp
            _ = H.subtype h⁻¹ * (H.subtype h * q'.out⁻¹) * q.out := by
              rw [← heq, mul_assoc]
            _ = (q'.out)⁻¹ * q.out := by simp
        have hmk := (QuotientGroup.eq).2 hmem
        simpa [Quotient.out_eq] using hmk
      exact Finsupp.single_eq_of_ne hne

/-- In the coset basis `basisCosets Λ H.subtype`, the identity coefficient of the `q`-th
`Λ[H]`-coordinate of any `x : Λ[G]` equals `x.coeff q.out⁻¹`. -/
theorem coeff_one_basisCosets_repr (H : Subgroup G) (x : MonoidAlgebra Λ G)
    (q : G ⧸ H.subtype.range) :
    let _ := (mapDomainRingHom Λ H.subtype).toModule
    ((TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective).repr x q).coeff 1 =
      x.coeff q.out⁻¹ := by
  classical
  let _ := (mapDomainRingHom Λ H.subtype).toModule
  let b := TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective
  let w := b.repr x
  have hsum :
      w.sum (fun q' z ↦ mapDomain H.subtype z * single q'.out⁻¹ (1 : Λ)) = x := by
    have hrepr := b.linearCombination_repr x
    simpa [Finsupp.linearCombination_apply, b, w, RingHom.toModule_smul] using hrepr
  have hcoeff := congrArg (fun u : MonoidAlgebra Λ G ↦ u.coeff q.out⁻¹) hsum
  rw [← hcoeff]
  have hfin :
      (w.sum fun q' z ↦ mapDomain H.subtype z * single q'.out⁻¹ (1 : Λ)).coeff q.out⁻¹ =
      ∑ q' ∈ w.support, (if q' = q then (w q').coeff 1 else 0) := by
    simp only [Finsupp.sum, coeff_sum, Finsupp.finsetSum_apply,
      coeff_mapDomain_subtype_mul_single_out_inv]
  rw [hfin]
  -- Fold the left-hand side into `(w q).coeff 1` so `simp` does not unfold `b` inside `w`.
  change (w q).coeff 1 = ∑ q' ∈ w.support, if q' = q then (w q').coeff 1 else 0
  by_cases hq : q ∈ w.support
  · rw [Finset.sum_eq_single q (fun q' _ hq' ↦ by simp [hq']) (fun hnot ↦ (hnot hq).elim)]
    simp
  · rw [Finset.sum_eq_zero fun q' hq' ↦ by
      have hne : q' ≠ q := fun hqq ↦ hq (hqq ▸ hq')
      simp [hne]]
    have hwq : w q = 0 := Finsupp.notMem_support_iff.1 hq
    simp [hwq]

end MonoidAlgebra

namespace LinearMap

section Restriction

open MonoidAlgebra

variable {Λ G : Type*} [Ring Λ] [Group G]

private theorem coeff_one_basisCosets_repr_mul (H : Subgroup G) (y : MonoidAlgebra Λ G)
    (q : G ⧸ H.subtype.range) :
    let _ := (mapDomainRingHom Λ H.subtype).toModule
    ((TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective).repr
      (TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective q * y) q).coeff 1 =
      y.coeff 1 := by
  let _ := (mapDomainRingHom Λ H.subtype).toModule
  simp [MonoidAlgebra.coeff_one_basisCosets_repr]

/-- **Subgroup restriction of the group-ring Hattori–Stallings trace** (Stacks Project,
Section 64.15, Lemma 64.15.2). Restricting a finite projective left `Λ[G]`-module `P` and a
`Λ[G]`-linear endomorphism `u` to a finite-index subgroup `H ≤ G` multiplies the group-ring trace
by `[G : H]`: `Tr_Λ^H(u, P) = H.index • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsGroupTrace_of_restrictSubgroup (H : Subgroup G) [H.FiniteIndex]
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra Λ G) P] [Module (MonoidAlgebra Λ H) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ H) P] [Module.Projective (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (u : Module.End (MonoidAlgebra Λ G) P) (u_H : Module.End (MonoidAlgebra Λ H) P)
    (hu : ∀ p, u_H p = u p) :
    hattoriStallingsGroupTrace Λ H P u_H =
      H.index • hattoriStallingsGroupTrace Λ G P u := by
  classical
  let φ := mapDomainRingHom Λ H.subtype
  let _ : Module (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) := φ.toModule
  have : Finite (G ⧸ H.subtype.range) := by
    rw [Subgroup.range_subtype]
    infer_instance
  let _ : Fintype (G ⧸ H.subtype.range) := Fintype.ofFinite _
  obtain ⟨r, π, i, -, -, hπi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let bCoset := TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective
  let bPi : Module.Basis ((_ : Fin r) × (G ⧸ H.subtype.range)) (MonoidAlgebra Λ H)
      (Fin r → MonoidAlgebra Λ G) := Pi.basis fun _ ↦ bCoset
  let i_H : P →ₗ[MonoidAlgebra Λ H] Fin r → MonoidAlgebra Λ G :=
    { toFun := i
      map_add' := map_add i
      map_smul' := fun c p ↦ by
        rw [RingHom.id_apply, hP, map_smul]
        ext k
        rfl }
  let π_H : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ H] P :=
    { toFun := π
      map_add' := map_add π
      map_smul' := fun c v ↦ by
        have hv : c • v = φ c • v := rfl
        rw [RingHom.id_apply, hv, map_smul, hP] }
  have hπi_H : π_H ∘ₗ i_H = .id := by
    ext p
    exact LinearMap.congr_fun hπi p
  have hcomp : ∀ v, (i_H ∘ₗ u_H ∘ₗ π_H) v = (i ∘ₗ u ∘ₗ π) v := fun v ↦ by
    simp [i_H, π_H, hu]
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_retract bPi i_H π_H hπi_H,
    hattoriStallingsTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra Λ G) (Fin r)) i π hπi,
    Module.Basis.hattoriStallingsTrace_apply, Module.Basis.hattoriStallingsTrace_apply,
    MonoidAlgebra.cyclicCoeffOne_mkQ, MonoidAlgebra.cyclicCoeffOne_mkQ]
  let T := i ∘ₗ u ∘ₗ π
  have hcard : Fintype.card (G ⧸ H.subtype.range) = H.index := by
    rw [← Nat.card_eq_fintype_card, Subgroup.range_subtype, Subgroup.index]
  rw [← map_nsmul, ← hcard]
  congr 1
  simp only [coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hdiag : ∀ q : G ⧸ H.subtype.range,
      ((bPi.repr ((i_H ∘ₗ u_H ∘ₗ π_H) (bPi ⟨k, q⟩))) ⟨k, q⟩).coeff 1 =
        (T (Pi.single k 1) k).coeff 1 := by
    intro q
    have hbPi : bPi ⟨k, q⟩ = bCoset q • Pi.single k (1 : MonoidAlgebra Λ G) := by
      ext j
      by_cases hjk : j = k
      · subst hjk
        simp [bPi]
      · simp [bPi, Pi.single_eq_of_ne hjk]
    have hT : (i_H ∘ₗ u_H ∘ₗ π_H) (bPi ⟨k, q⟩) = T (bCoset q • Pi.single k 1) := by
      rw [hcomp, hbPi]
    rw [hT, map_smul]
    simpa [bPi, bCoset] using coeff_one_basisCosets_repr_mul H (T (Pi.single k 1) k) q
  rw [Finset.sum_congr rfl fun q _ ↦ hdiag q]
  simp [T]

/-- **Forgetting a finite group action multiplies the group-ring trace by `|G|`** (Stacks Project,
Lemma 64.15.2 for the trivial subgroup). For a finite group `G` and a `Λ[G]`-linear endomorphism
`u` of a finite projective left `Λ[G]`-module `P`, the `Λ`-trace of `u` equals `|G|` times its
group-ring trace: `Tr_Λ(u, P) = Nat.card G • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace [Finite G]
    {P : Type*} [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite Λ P] [Module.Projective Λ P]
    (u : Module.End (MonoidAlgebra Λ G) P) :
    hattoriStallingsTrace Λ P (u.restrictScalars Λ) =
      Nat.card G • hattoriStallingsGroupTrace Λ G P u := by
  classical
  let H : Subgroup G := ⊥
  let φ := mapDomainRingHom Λ H.subtype
  let _ : Module (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) := φ.toModule
  let _ : Module (MonoidAlgebra Λ H) P := Module.compHom P φ
  obtain ⟨_, hHP, _, hfinH, hprojH⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) H (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let eBot : MonoidAlgebra Λ H ≃+* Λ :=
    RingEquiv.ofRingHom (augmentation Λ H) singleOneRingHom
      (by ext c; simp)
      (by
        apply ringHom_ext
        · intro c
          simp
        · intro h
          have hh : h = 1 := Subsingleton.elim h 1
          subst hh
          simp)
  let _ := RingHomInvPair.of_ringEquiv eBot
  let _ := RingHomInvPair.of_ringEquiv_symm eBot
  have hcomp : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = φ r • p := fun _ _ ↦ rfl
  let j : P ≃ₛₗ[(eBot : MonoidAlgebra Λ H →+* Λ)] P :=
    { toFun := fun p ↦ p
      invFun := fun p ↦ p
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r p ↦ by
        induction r using induction_linear with
        | zero => simp
        | add x y hx hy => rw [add_smul, map_add, add_smul, hx, hy]
        | single h c =>
          have hh : h = 1 := Subsingleton.elim h 1
          subst hh
          rw [hcomp]
          simp only [φ, mapDomainRingHom_apply, mapDomain_single, map_one]
          have hsmul : (MonoidAlgebra.single (1 : G) c : MonoidAlgebra Λ G) • p = c • p := by
            rw [← smul_one_smul (MonoidAlgebra Λ G) c p, one_def, smul_single, smul_eq_mul, mul_one]
          have he : (eBot : MonoidAlgebra Λ H →+* Λ) (MonoidAlgebra.single (1 : H) c) = c := by
            simp [eBot]
          rw [hsmul, he] }
  let u_H : Module.End (MonoidAlgebra Λ H) P := u.restrictScalars (MonoidAlgebra Λ H)
  have htr : hattoriStallingsTrace Λ P (u.restrictScalars Λ) =
      hattoriStallingsGroupTrace Λ H P u_H := by
    rw [j.hattoriStallingsTrace_eq_map (T := u_H) (T' := u.restrictScalars Λ) (fun _ ↦ rfl),
      hattoriStallingsGroupTrace_apply]
    obtain ⟨x, hx_mk⟩ := Submodule.Quotient.mk_surjective _ (hattoriStallingsTrace _ P u_H)
    rw [← hx_mk, TauCeti.cyclicQuotientRingHomMap_mk, cyclicCoeffOne_mk]
    clear hx_mk
    have hx : (eBot : MonoidAlgebra Λ H →+* Λ) x = x.coeff 1 := by
      induction x using induction_linear with
      | zero => simp
      | add a b ha hb => rw [map_add, coeff_add, Finsupp.add_apply, ha, hb]
      | single h c =>
        have hh : h = 1 := Subsingleton.elim h 1
        subst hh
        simp [eBot]
    rw [hx]
  rw [htr, hattoriStallingsGroupTrace_of_restrictSubgroup H (fun _ _ ↦ rfl) u u_H (fun _ ↦ rfl),
    Subgroup.index_bot]

end Restriction

section CommRing

variable (A G P : Type*) [CommRing A] [Group G] [AddCommGroup P] [Module (MonoidAlgebra A G) P]
  [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]

/-- **The scalar-valued group-ring trace over a commutative ring** `Tr_A^G(u, P) ∈ A`. The group
`G` need not be abelian, so `A[G]` itself may be noncommutative; the trace is obtained by composing
`hattoriStallingsGroupTrace A G P` with `A / [A, A] ≃ A`. -/
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

/-- Scalar extension of `projectiveGroupTrace` along a homomorphism `φ : A →+* B` of commutative
rings. -/
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
theorem projectiveGroupTrace_of_restrictSubgroup (H : Subgroup G) [H.FiniteIndex]
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

/-- For a finite group `G` over a commutative ring `A`, the `A`-projective trace of a `A[G]`-linear
endomorphism equals `|G|` times its `A`-valued group-ring trace. -/
theorem projectiveTrace_restrictScalars_eq_card_mul_projectiveGroupTrace [Finite G]
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
