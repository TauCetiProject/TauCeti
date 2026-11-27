/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.MonoidAlgebra.CyclicQuotient
public import TauCeti.LinearAlgebra.Trace.HattoriStallings
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.Basis
import TauCeti.Algebra.MonoidAlgebra.CosetBasis

/-!
# Group-ring Hattori–Stallings traces

For a group `G` and an arbitrary ring `Λ`, composing the Hattori–Stallings trace of a finite
projective left `Λ[G]`-module `P` with the identity-coefficient functional
`TauCeti.MonoidAlgebra.cyclicCoeffOne Λ G : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (from
`TauCeti.Algebra.MonoidAlgebra.CyclicQuotient`; Stacks Project, Section 64.15, Lemma 64.15.1)
defines `LinearMap.hattoriStallingsGroupTrace Λ G P` and, over a commutative ring `A`,
`LinearMap.projectiveGroupTrace A G P : End_{A[G]}(P) →ₗ[A] A` without dividing by `|G|`.

## Main definitions and results

* `LinearMap.hattoriStallingsGroupTrace` and `LinearMap.projectiveGroupTrace`: group-ring traces
  over arbitrary `Λ` and commutative `A`.
* `LinearMap.hattoriStallingsGroupTrace_balancedExtension_mapDomainRingHom_of_injective`:
  induction along an injective group homomorphism `p : H →* G` preserves the trace (Lemma 64.15.3).
* `LinearMap.hattoriStallingsGroupTrace_eq_index_nsmul`: restriction to `H ≤ G` multiplies the
  trace by `H.index` (Lemma 64.15.2).
* `LinearMap.hattoriStallingsTrace_eq_card_nsmul_hattoriStallingsGroupTrace_of_eqLocus` and
  `LinearMap.hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace`:
  automorphism-twisted traces and forgetting the `G`-action (`Tr_Λ(u, P) = |G| • Tr_Λ^G(u, P)`).

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.1–64.15.3).
* P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
-/

public section

noncomputable section

open MonoidAlgebra
open TauCeti.MonoidAlgebra (cyclicCoeffOne cyclicCoeffOne_mk cyclicCoeffOne_mapRingHom
  cyclicCoeffOne_mapDomainRingHom_of_injective)

namespace LinearMap

section NoncommRing

variable (Λ G P : Type*) [Ring Λ] [Group G] [AddCommGroup P] [Module Λ[G] P]
  [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]

/-- **The group-ring Hattori–Stallings trace** `Tr_Λ^G(u, P) ∈ Λ / [Λ, Λ]` of a `Λ[G]`-linear
endomorphism `u` of a finite projective left `Λ[G]`-module `P` (Stacks Project, Section 64.15). -/
def hattoriStallingsGroupTrace : Module.End Λ[G] P →+ TauCeti.cyclicQuotient ℤ Λ :=
  (cyclicCoeffOne Λ G).toAddMonoidHom.comp (hattoriStallingsTrace Λ[G] P)

theorem hattoriStallingsGroupTrace_apply (u : Module.End Λ[G] P) :
    hattoriStallingsGroupTrace Λ G P u =
      cyclicCoeffOne Λ G (hattoriStallingsTrace Λ[G] P u) := by rfl

variable {Λ G P}

section TwoModules

variable {Q : Type*} [AddCommGroup Q] [Module Λ[G] Q]
  [Module.Finite Λ[G] Q] [Module.Projective Λ[G] Q]

/-- Cyclicity of `hattoriStallingsGroupTrace` across finite projective left `Λ[G]`-modules. -/
theorem hattoriStallingsGroupTrace_comp_comm (u : P →ₗ[Λ[G]] Q) (v : Q →ₗ[Λ[G]] P) :
    hattoriStallingsGroupTrace Λ G P (v ∘ₗ u) = hattoriStallingsGroupTrace Λ G Q (u ∘ₗ v) := by
  rw [hattoriStallingsGroupTrace_apply, hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_comp_comm]

/-- Conjugation invariance of `hattoriStallingsGroupTrace`. -/
@[simp] theorem hattoriStallingsGroupTrace_conj (u : Module.End Λ[G] P) (e : P ≃ₗ[Λ[G]] Q) :
    hattoriStallingsGroupTrace Λ G Q (e.conjRingEquiv u) = hattoriStallingsGroupTrace Λ G P u := by
  simp [hattoriStallingsGroupTrace_apply]

/-- Additivity of `hattoriStallingsGroupTrace` on direct products. -/
@[simp] theorem hattoriStallingsGroupTrace_prodMap (u : Module.End Λ[G] P) (v : Module.End Λ[G] Q) :
    hattoriStallingsGroupTrace Λ G (P × Q) (u.prodMap v) =
      hattoriStallingsGroupTrace Λ G P u + hattoriStallingsGroupTrace Λ G Q v := by
  simp [hattoriStallingsGroupTrace_apply]

end TwoModules

/-- On the zero module `hattoriStallingsGroupTrace` vanishes. -/
@[simp] theorem hattoriStallingsGroupTrace_eq_zero_of_subsingleton [Subsingleton P]
    (u : Module.End Λ[G] P) : hattoriStallingsGroupTrace Λ G P u = 0 := by
  simp [hattoriStallingsGroupTrace_apply]

/-- **Scalar extension along `φ : Λ →+* Λ'`.** -/
@[simp] theorem hattoriStallingsGroupTrace_balancedExtension_mapRingHom {Λ' : Type*} [Ring Λ']
    (φ : Λ →+* Λ') (u : Module.End Λ[G] P) :
    hattoriStallingsGroupTrace Λ' G (TauCeti.BalancedExtension (mapRingHom G φ) P)
        (TauCeti.BalancedExtension.map (mapRingHom G φ) u) =
      TauCeti.cyclicQuotientRingHomMap φ (hattoriStallingsGroupTrace Λ G P u) := by
  simp [hattoriStallingsGroupTrace_apply]

end NoncommRing

section RegularAndInduction

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- On the regular left `Λ[G]`-module `Λ[G]`, `Tr_Λ^G(u) = [(u 1).coeff 1]`. -/
@[simp] theorem hattoriStallingsGroupTrace_regular (u : Module.End Λ[G] Λ[G]) :
    hattoriStallingsGroupTrace Λ G Λ[G] u = Submodule.Quotient.mk ((u 1).coeff 1) := by
  rw [hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_basis (Module.Basis.singleton Unit Λ[G]),
    Module.Basis.hattoriStallingsTrace_apply, Submodule.mkQ_apply, cyclicCoeffOne_mk]; simp

/-- **Induction along an injective group homomorphism** (Stacks Project, Section 64.15,
Lemma 64.15.3): `Tr_Λ^G(Λ[G] ⊗_{Λ[H]} u) = Tr_Λ^H(u)`. -/
@[simp] theorem hattoriStallingsGroupTrace_balancedExtension_mapDomainRingHom_of_injective
    {H Q : Type*} [Group H] [AddCommGroup Q] [Module Λ[H] Q]
    [Module.Finite Λ[H] Q] [Module.Projective Λ[H] Q]
    {p : H →* G} (hp : Function.Injective p) (u : Module.End Λ[H] Q) :
    hattoriStallingsGroupTrace Λ G (TauCeti.BalancedExtension (mapDomainRingHom Λ p) Q)
        (TauCeti.BalancedExtension.map (mapDomainRingHom Λ p) u) =
      hattoriStallingsGroupTrace Λ H Q u := by
  simp [hattoriStallingsGroupTrace_apply, hp]

end RegularAndInduction

end LinearMap

namespace LinearEquiv

/-- **Group-isomorphism transport of `hattoriStallingsGroupTrace`.** -/
theorem hattoriStallingsGroupTrace_eq_of_mapDomainRingHom {Λ H G P P' : Type*} [Ring Λ] [Group H]
    [Group G] [AddCommGroup P] [Module Λ[H] P] [AddCommGroup P'] [Module Λ[G] P']
    [Module.Finite Λ[H] P] [Module.Projective Λ[H] P] [Module.Finite Λ[G] P']
    [Module.Projective Λ[G] P'] {σ : Λ[H] →+* Λ[G]} {σ' : Λ[G] →+* Λ[H]}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (j : P ≃ₛₗ[σ] P') {e : H ≃* G}
    (hσ : σ = mapDomainRingHom Λ e.toMonoidHom) {u : Module.End Λ[H] P} {u' : Module.End Λ[G] P'}
    (h : ∀ x, u' (j x) = j (u x)) :
    LinearMap.hattoriStallingsGroupTrace Λ G P' u' =
      LinearMap.hattoriStallingsGroupTrace Λ H P u := by
  rw [LinearMap.hattoriStallingsGroupTrace_apply,
    j.hattoriStallingsTrace_eq_cyclicQuotientRingHomMap h, hσ,
    cyclicCoeffOne_mapDomainRingHom_of_injective e.injective,
    ← LinearMap.hattoriStallingsGroupTrace_apply]

end LinearEquiv

namespace LinearMap

section Restriction

variable {Λ G : Type*} [Ring Λ] [Group G]

variable {P : Type*} [AddCommGroup P] [Module Λ[G] P]

private theorem pi_single_smul_eq {r : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P)
    (k : Fin r) (g : G) :
    π (Pi.single k (MonoidAlgebra.single g (1 : Λ))) =
      (MonoidAlgebra.single g (1 : Λ) : Λ[G]) • π (Pi.single k 1) := by
  rw [← map_smul π, ← Pi.single_smul', smul_eq_mul, mul_one]

/-- Evaluating `hattoriStallingsGroupTrace Λ H P u_H` on a `Λ[G]`-free retract `(π, i)` of `P` via
the coset basis `basisCosets Λ H.subtype`. -/
theorem hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract (H : Subgroup G)
    [Module Λ[H] P] [Module.Finite Λ[H] P] [Module.Projective Λ[H] P]
    (hP : ∀ (r : Λ[H]) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    {r : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (u_H : Module.End Λ[H] P) [Fintype (G ⧸ H.subtype.range)] :
    hattoriStallingsGroupTrace Λ H P u_H =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ H.subtype.range,
          (i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : Λ[G]) •
            π (Pi.single k 1))) k).coeff q.out⁻¹) := by
  classical
  let _ : Module Λ[H] Λ[G] := (mapDomainRingHom Λ H.subtype).toModule
  have hsmul (c : Λ[H]) (v : Fin r → Λ[G]) :
      c • v = mapDomainRingHom Λ H.subtype c • v := by
    ext k; rw [Pi.smul_apply, Pi.smul_apply, RingHom.toModule_smul, smul_eq_mul]
  let i_H : P →ₗ[Λ[H]] Fin r → Λ[G] :=
    { toFun := i, map_add' := map_add i,
      map_smul' := fun c p ↦ by rw [RingHom.id_apply, hP, map_smul, hsmul] }
  let π_H : (Fin r → Λ[G]) →ₗ[Λ[H]] P :=
    { toFun := π, map_add' := map_add π,
      map_smul' := fun c v ↦ by rw [RingHom.id_apply, hsmul, map_smul, hP] }
  let bPi : Module.Basis ((_ : Fin r) × (G ⧸ H.subtype.range)) Λ[H] (Fin r → Λ[G]) :=
    Pi.basis fun _ ↦ TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective
  rw [hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_retract bPi i_H π_H
      (LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p),
    Module.Basis.hattoriStallingsTrace_apply, Submodule.mkQ_apply, cyclicCoeffOne_mk]
  congr 1; simp only [coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hπ : π_H (bPi ⟨k, q⟩) =
      (MonoidAlgebra.single q.out⁻¹ (1 : Λ) : Λ[G]) • π (Pi.single k 1) := by
    simpa [π_H, bPi] using pi_single_smul_eq π k q.out⁻¹
  rw [comp_apply, comp_apply, hπ]; simp [bPi, i_H]

/-- **Subgroup restriction of the group-ring Hattori–Stallings trace** (Stacks Project,
Section 64.15, Lemma 64.15.2): `Tr_Λ^H(u, P) = H.index • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsGroupTrace_eq_index_nsmul (H : Subgroup G)
    [Module Λ[H] P] [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
    [Module.Finite Λ[H] P] [Module.Projective Λ[H] P]
    (hP : ∀ (r : Λ[H]) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (u : Module.End Λ[G] P) (u_H : Module.End Λ[H] P) (hu : ∀ p, u_H p = u p) :
    hattoriStallingsGroupTrace Λ H P u_H = H.index • hattoriStallingsGroupTrace Λ G P u := by
  rcases finite_or_infinite (G ⧸ H) with _ | _
  · classical
    have : Finite (G ⧸ H.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    let _ : Fintype (G ⧸ H.subtype.range) := Fintype.ofFinite _
    obtain ⟨r, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ[G] P
    have hcard : Fintype.card (G ⧸ H.subtype.range) = H.index := by
      rw [← Nat.card_eq_fintype_card, Subgroup.range_subtype, Subgroup.index]
    rw [hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract H hP π i hπi u_H,
      hattoriStallingsGroupTrace_apply,
      hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ[G] (Fin r)) i π hπi,
      Module.Basis.hattoriStallingsTrace_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      cyclicCoeffOne_mk, ← hcard]
    simp only [← (TauCeti.commutatorSubmodule ℤ Λ).mkQ_apply, ← map_nsmul]
    congr 1; simp only [coeff_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hq (q : G ⧸ H.subtype.range) :
        (i (u_H ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : Λ[G]) •
            π (Pi.single k 1))) k).coeff q.out⁻¹ = (i (u (π (Pi.single k 1))) k).coeff 1 := by
      simp [hu, smul_eq_mul]
    simp [hq]
  · have := H.subsingleton_of_infinite_quotient P hP; simp

/-- **Trace of an automorphism-twisted endomorphism of a finite projective `Λ[G]`-module.** If
`σ : G ≃* G`, `Z = σ.toMonoidHom.eqLocus (.id G)`, and `φ : P →ₗ[Λ] P` satisfies
`φ (single g 1 • p) = single (σ g) 1 • φ p`, then `Tr_Λ(φ, P) = |Z| • Tr_Λ^Z(φ, P)`. -/
theorem hattoriStallingsTrace_eq_card_nsmul_hattoriStallingsGroupTrace_of_eqLocus
    {σ : G ≃* G} {Z : Subgroup G} (hZ : Z = σ.toMonoidHom.eqLocus (.id G)) [Module Λ P]
    [IsScalarTower Λ Λ[G] P] [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
    [Module.Finite Λ P] [Module.Projective Λ P] [Module Λ[Z] P]
    [Module.Finite Λ[Z] P] [Module.Projective Λ[Z] P]
    (hP : ∀ (r : Λ[Z]) (p : P), r • p = mapDomainRingHom Λ Z.subtype r • p)
    (φ : Module.End Λ P) (φ_Z : Module.End Λ[Z] P)
    (hφ : ∀ (g : G) (p : P),
      φ (MonoidAlgebra.single g (1 : Λ) • p) = MonoidAlgebra.single (σ g) (1 : Λ) • φ p)
    (hφZ : ∀ p, φ_Z p = φ p) :
    hattoriStallingsTrace Λ P φ = Nat.card Z • hattoriStallingsGroupTrace Λ Z P φ_Z := by
  rcases finite_or_infinite G with _ | _
  · subst hZ; classical
    let Z := σ.toMonoidHom.eqLocus (.id G); let _ : Fintype G := Fintype.ofFinite G
    have : Finite (G ⧸ Z.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    let _ : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
    obtain ⟨r, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ[G] P
    let i_Λ := i.restrictScalars Λ; let π_Λ := π.restrictScalars Λ
    let bΛ : Module.Basis ((_ : Fin r) × G) Λ (Fin r → Λ[G]) :=
      Pi.basis fun _ ↦ MonoidAlgebra.basis G Λ
    rw [hattoriStallingsTrace_eq_of_retract bΛ i_Λ π_Λ
        (LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p),
      Module.Basis.hattoriStallingsTrace_apply,
      hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract Z hP π i hπi φ_Z, ← map_nsmul]
    congr 1; simp only [Fintype.sum_sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let yk := i (φ (π (Pi.single k 1))) k
    have himg (x : G) :
        i (φ ((MonoidAlgebra.single x (1 : Λ) : Λ[G]) • π (Pi.single k 1))) k =
          MonoidAlgebra.single (σ x) (1 : Λ) * yk := by
      simp [hφ, yk, smul_eq_mul]
    have hLHS (g : G) :
        (bΛ.repr ((i_Λ ∘ₗ φ ∘ₗ π_Λ) (bΛ ⟨k, g⟩))) ⟨k, g⟩ = yk.coeff ((σ g)⁻¹ * g) := by
      have hπ : π_Λ (bΛ ⟨k, g⟩) = MonoidAlgebra.single g (1 : Λ) • π (Pi.single k 1) := by
        simpa [π_Λ, bΛ] using pi_single_smul_eq π k g
      have hrepr (v : Fin r → Λ[G]) : (bΛ.repr v) ⟨k, g⟩ = (v k).coeff g := by simp [bΛ]
      rw [hrepr, comp_apply, comp_apply, hπ, restrictScalars_apply, himg, coeff_single_mul_apply,
        one_mul]
    have hRHS (q : G ⧸ Z.subtype.range) :
        (i (φ_Z ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : Λ[G]) •
            π (Pi.single k 1))) k).coeff q.out⁻¹ = yk.coeff ((σ q.out⁻¹)⁻¹ * q.out⁻¹) := by
      rw [hφZ, himg, coeff_single_mul_apply, one_mul]
    simp only [hLHS, hRHS, ← Finset.smul_sum]
    have hcard : Nat.card Z.subtype.range = Nat.card Z := by rw [Subgroup.range_subtype]
    exact (Subgroup.sum_twisted_eq_card_nsmul Z.subtype.range σ.toMonoidHom
      (by rintro _ ⟨z, rfl⟩; exact MonoidHom.mem_eqLocusM.1 z.property) yk.coeff).trans
      (by rw [hcard]; rfl)
  · have := TauCeti.MonoidAlgebra.subsingleton_of_infinite_group Λ G P; simp

/-- **Forgetting a group action multiplies the group-ring trace by `|G|`** (Stacks Project,
Lemma 64.15.2 for the trivial subgroup): `Tr_Λ(u, P) = Nat.card G • Tr_Λ^G(u, P)`. -/
theorem hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace
    [Module Λ P] [IsScalarTower Λ Λ[G] P] [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
    [Module.Finite Λ P] [Module.Projective Λ P] (u : Module.End Λ[G] P) :
    hattoriStallingsTrace Λ P (u.restrictScalars Λ) =
      Nat.card G • hattoriStallingsGroupTrace Λ G P u := by
  let Z : Subgroup G := ⊤; let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module Λ[Z] Λ[G] := φZ.toModule; let _ : Module Λ[Z] P := Module.compHom P φZ
  obtain ⟨_, _, _, _⟩ := Subgroup.restrictSubgroup_compHom_finite_projective (R := Λ) Z P
  have hZ : Z = (MulEquiv.refl G).toMonoidHom.eqLocus (.id G) := (MonoidHom.eqLocus_same _).symm
  let u_Z : Module.End Λ[Z] P :=
    { toFun := u, map_add' := map_add u, map_smul' := fun r p ↦ map_smul u (φZ r) p }
  rw [hattoriStallingsTrace_eq_card_nsmul_hattoriStallingsGroupTrace_of_eqLocus hZ (fun _ _ ↦ rfl)
      (u.restrictScalars Λ) u_Z (fun _ _ ↦ by simp) (fun _ ↦ rfl),
    hattoriStallingsGroupTrace_eq_index_nsmul Z (fun _ _ ↦ rfl) u u_Z (fun _ ↦ rfl),
    Subgroup.index_top, one_smul, Subgroup.card_top]

end Restriction

section CommRing

variable (A G P : Type*) [CommRing A] [Group G] [AddCommGroup P] [Module A P] [Module A[G] P]
  [IsScalarTower A A[G] P] [SMulCommClass A[G] A P]
  [Module.Finite A[G] P] [Module.Projective A[G] P]

/-- **The scalar-valued group-ring trace over a commutative ring** `Tr_A^G(u, P) ∈ A`. -/
def projectiveGroupTrace : Module.End A[G] P →ₗ[A] A where
  toFun u := TauCeti.cyclicQuotientEquivOfComm ℤ A (hattoriStallingsGroupTrace A G P u)
  map_add' _ _ := by simp only [map_add]
  map_smul' a u := by
    classical
    obtain ⟨n, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective A[G] P
    simp only [RingHom.id_apply, hattoriStallingsGroupTrace_apply,
      hattoriStallingsTrace_eq_of_retract (Pi.basisFun A[G] (Fin n)) i π hπi,
      Module.Basis.hattoriStallingsTrace_apply, Submodule.mkQ_apply, cyclicCoeffOne_mk,
      TauCeti.cyclicQuotientEquivOfComm_mk, coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ by simp

variable {A G P}

theorem projectiveGroupTrace_apply (u : Module.End A[G] P) :
    projectiveGroupTrace A G P u =
      TauCeti.cyclicQuotientEquivOfComm ℤ A (hattoriStallingsGroupTrace A G P u) := by rfl

theorem hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace (u : Module.End A[G] P) :
    hattoriStallingsGroupTrace A G P u =
      (TauCeti.commutatorSubmodule ℤ A).mkQ (projectiveGroupTrace A G P u) := by
  simp [Submodule.mkQ_apply, projectiveGroupTrace_apply,
    ← TauCeti.cyclicQuotientEquivOfComm_symm_apply]

section TwoModules

variable {Q : Type*} [AddCommGroup Q] [Module A Q] [Module A[G] Q]
  [IsScalarTower A A[G] Q] [SMulCommClass A[G] A Q]
  [Module.Finite A[G] Q] [Module.Projective A[G] Q]

/-- Cyclicity of `projectiveGroupTrace` across finite projective left `A[G]`-modules. -/
theorem projectiveGroupTrace_comp_comm (u : P →ₗ[A[G]] Q) (v : Q →ₗ[A[G]] P) :
    projectiveGroupTrace A G P (v ∘ₗ u) = projectiveGroupTrace A G Q (u ∘ₗ v) := by
  rw [projectiveGroupTrace_apply, projectiveGroupTrace_apply, hattoriStallingsGroupTrace_comp_comm]

/-- Conjugation invariance of `projectiveGroupTrace`. -/
@[simp] theorem projectiveGroupTrace_conj (u : Module.End A[G] P) (e : P ≃ₗ[A[G]] Q) :
    projectiveGroupTrace A G Q (e.conjRingEquiv u) = projectiveGroupTrace A G P u := by
  simp [projectiveGroupTrace_apply]

/-- Additivity of `projectiveGroupTrace` on direct products. -/
@[simp] theorem projectiveGroupTrace_prodMap (u : Module.End A[G] P) (v : Module.End A[G] Q) :
    projectiveGroupTrace A G (P × Q) (u.prodMap v) =
      projectiveGroupTrace A G P u + projectiveGroupTrace A G Q v := by
  simp [projectiveGroupTrace_apply]

end TwoModules

/-- On the zero module `projectiveGroupTrace` vanishes. -/
@[simp] theorem projectiveGroupTrace_eq_zero_of_subsingleton [Subsingleton P]
    (u : Module.End A[G] P) : projectiveGroupTrace A G P u = 0 := by
  simp [projectiveGroupTrace_apply]

/-- On the regular left `A[G]`-module `A[G]`, `Tr_A^G(u) = (u 1).coeff 1`. -/
@[simp] theorem projectiveGroupTrace_regular (u : Module.End A[G] A[G]) :
    projectiveGroupTrace A G A[G] u = (u 1).coeff 1 := by simp [projectiveGroupTrace_apply]

section
attribute [local instance low] TauCeti.BalancedExtension.moduleBase

/-- Scalar extension of `projectiveGroupTrace` along `φ : A →+* B`. -/
@[simp] theorem projectiveGroupTrace_balancedExtension_mapRingHom {B : Type*} [CommRing B]
    (φ : A →+* B) (u : Module.End A[G] P) :
    projectiveGroupTrace B G (TauCeti.BalancedExtension (mapRingHom G φ) P)
        (TauCeti.BalancedExtension.map (mapRingHom G φ) u) =
      φ (projectiveGroupTrace A G P u) := by
  simp [projectiveGroupTrace_apply]

/-- Induction along an injective group homomorphism preserves `projectiveGroupTrace`. -/
@[simp] theorem projectiveGroupTrace_balancedExtension_mapDomainRingHom_of_injective
    {H Q : Type*} [Group H] [AddCommGroup Q] [Module A Q] [Module A[H] Q]
    [IsScalarTower A A[H] Q] [SMulCommClass A[H] A Q]
    [Module.Finite A[H] Q] [Module.Projective A[H] Q]
    {p : H →* G} (hp : Function.Injective p) (u : Module.End A[H] Q) :
    projectiveGroupTrace A G (TauCeti.BalancedExtension (mapDomainRingHom A p) Q)
        (TauCeti.BalancedExtension.map (mapDomainRingHom A p) u) =
      projectiveGroupTrace A H Q u := by simp [projectiveGroupTrace_apply, hp]

end

/-- Subgroup restriction multiplies `projectiveGroupTrace` by `[G : H]`. -/
theorem projectiveGroupTrace_eq_index_mul (H : Subgroup G)
    [Module A[H] P] [IsScalarTower A A[H] P] [SMulCommClass A[H] A P]
    [Module.Finite A[H] P] [Module.Projective A[H] P]
    (hP : ∀ (r : A[H]) (p : P), r • p = mapDomainRingHom A H.subtype r • p)
    (u : Module.End A[G] P) (u_H : Module.End A[H] P) (hu : ∀ p, u_H p = u p) :
    projectiveGroupTrace A H P u_H = H.index * projectiveGroupTrace A G P u := by
  simpa [hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace, map_nsmul, nsmul_eq_mul] using
    congrArg (TauCeti.cyclicQuotientEquivOfComm ℤ A).toAddMonoidHom
      (hattoriStallingsGroupTrace_eq_index_nsmul H hP u u_H hu)

/-- Over a commutative ring `A`, `Tr_A(u, P) = |G| * Tr_A^G(u, P)`. -/
theorem projectiveTrace_restrictScalars_eq_card_mul_projectiveGroupTrace
    [Module.Finite A P] [Module.Projective A P]
    (u : Module.End A[G] P) :
    projectiveTrace A P (u.restrictScalars A) =
      (Nat.card G : A) * projectiveGroupTrace A G P u := by
  simpa [hattoriStallingsTrace_eq_projectiveTrace,
    hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace, map_nsmul, nsmul_eq_mul] using
    congrArg (TauCeti.cyclicQuotientEquivOfComm ℤ A).toAddMonoidHom
      (hattoriStallingsTrace_restrictScalars_eq_card_nsmul_hattoriStallingsGroupTrace u)

end CommRing

end LinearMap

end
