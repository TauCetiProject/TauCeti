/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.Algebra.MonoidAlgebra.Coinvariants
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Data.ZMod.Torsion
public import TauCeti.LinearAlgebra.Trace.GroupRing.Basic

/-!
# Hattori–Stallings traces for monoid extensions over `ℕ`

Let `1 → G → Γtilde → ℤ → 1` be an extension of groups with `G` finite (`ι : G →* Γtilde`
injective, `deg : Γtilde →* Multiplicative ℤ`, and `ι.range = deg.ker`), and let
`Γ = nonnegSubmonoid deg = deg⁻¹(ℕ)` be the submonoid of elements of nonnegative degree.
Let `Λ` be a possibly noncommutative ring and `P` a left `Λ[Γ]`-module that is finitely generated
and projective when restricted to `Λ[G]`.

For any `γ ∈ Γ`, conjugation by `γ` induces an automorphism `conjAut` of `G` whose fixed-point
subgroup is the centralizer `Z_γ = centralizerSubgroup ι γ.1 = { g ∈ G | ι g * γ = γ * ι g }`.
Restricting `P` to `Z_γ` makes `P` finite projective over `Λ[Z_γ]` and makes the action of `γ`
`Λ[Z_γ]`-linear, yielding a well-defined centralizer trace
`centralizerGroupTrace Λ ι deg hker hPG γ ∈ Λ / [Λ, Λ]` without dividing by `|G|` or `|Z_γ|`.

## Main definitions

* `MulEquiv.fixedPointsSubgroup`: the subgroup `{ g : G | σ g = g }` of fixed points of
  `σ : G ≃* G`.
* `TauCeti.BalancedExtension.monoidAlgebraEquiv`: identification of `Λ'[M] ⊗_{Λ[M]} P` with
  `Λ' ⊗_Λ P` along a coefficient ring homomorphism `φ : Λ →+* Λ'`.
* `TauCeti.MonoidExtension.nonnegSubmonoid`: the submonoid `Γ = { γ : Γtilde | 0 ≤ toAdd (deg γ) }`.
* `TauCeti.MonoidExtension.conjAut` and `TauCeti.MonoidExtension.centralizerSubgroup`: conjugation
  on `G` and the centralizer `Z_γ ≤ G`.
* `TauCeti.MonoidExtension.centralizerGroupTrace` and
  `TauCeti.MonoidExtension.centralizerProjectiveGroupTrace`: the group-ring trace
  `Tr_Λ^{Z_γ}(γ, P)`.
* `TauCeti.MonoidExtension.DegreeFiber`, `TauCeti.MonoidExtension.ConjClasses`, and
  `TauCeti.MonoidExtension.conjClassGroupTrace`: `G`-conjugacy classes on
  `{ γ ∈ Γ // deg γ = ofAdd d }` and the descended trace.
* `TauCeti.MonoidExtension.coinvariantEnd`: the `Λ`-linear endomorphism of `Coinvariants Λ G P`
  induced by `γ₀ ∈ Γ`.

## Main results

* `LinearMap.hattoriStallingsTrace_of_twistedSMul`: for any finite group `G`, automorphism
  `σ : G ≃* G`, and `Λ`-linear endomorphism `φ` of a finite projective `Λ[G]`-module satisfying
  `φ (g • p) = σ g • φ p`, `Tr_Λ(φ, P) = |G^σ| • Tr_Λ^{G^σ}(φ, P)`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul`:
  `Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)` (Stacks Project, Section 64.15, Lemma 64.15.4).
* `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses`:
  `Tr_Λ(γ₀, P_G) = ∑_{[γ]} Tr_Λ^{Z_γ}(γ, P)` over `G`-conjugacy classes of elements in `Γ` of the
  same degree as `γ₀`, in particular degree `1` (Stacks Project, Section 64.15, Lemma 64.15.5).
* `TauCeti.MonoidExtension.centralizerProjectiveGroupTrace_zmod_eq_castHom`: `ℤ/ℓⁿ` coefficient
  descent from `ℤ/ℓ^{n+v}` when `ℓ^{v+1} ∤ |Z_γ|` (Stacks Project, Section 64.15, Lemma 64.15.9).

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.4, 64.15.5, and 64.15.9).
* P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
* A. Grothendieck et al., *Cohomologie ℓ-adique et fonctions L* (SGA 5), Exposé III.
-/

public section

noncomputable section

/-! ### Fixed-point subgroup and twisted group-ring traces -/

namespace MulEquiv

/-- The subgroup of elements fixed by a group automorphism `σ : G ≃* G`. -/
def fixedPointsSubgroup {G : Type*} [Group G] (σ : G ≃* G) : Subgroup G where
  carrier := { g : G | σ g = g }
  one_mem' := map_one σ
  mul_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' ha := by
    simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
    rw [ha]

@[simp]
theorem mem_fixedPointsSubgroup {G : Type*} [Group G] {σ : G ≃* G} {g : G} :
    g ∈ σ.fixedPointsSubgroup ↔ σ g = g :=
  Iff.rfl

end MulEquiv

namespace LinearMap

section TwistedTrace

open MonoidAlgebra

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- An endomorphism `φ : P →ₗ[Λ] P` satisfying `φ (single g 1 • p) = single (σ g) 1 • φ p` restricts
to a `Λ[H]`-linear endomorphism on any subgroup `H ≤ σ.fixedPointsSubgroup`. -/
def restrictFixedSubgroup {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    {σ : G ≃* G} {H : Subgroup G} (hle : H ≤ σ.fixedPointsSubgroup)
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
      rw [single_smul_eq_smul_single_one_smul, map_smul, hφ, hh,
        ← single_smul_eq_smul_single_one_smul]

@[simp]
theorem restrictFixedSubgroup_apply {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    {σ : G ≃* G} {H : Subgroup G} (hle : H ≤ σ.fixedPointsSubgroup)
    [Module (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (p : P), r • p = mapDomainRingHom Λ H.subtype r • p)
    (φ : Module.End Λ P)
    (hφ : ∀ (g : G) (p : P), φ (MonoidAlgebra.single g (1 : Λ) • p) =
      MonoidAlgebra.single (σ g) (1 : Λ) • φ p) (p : P) :
    restrictFixedSubgroup hle hP φ hφ p = φ p :=
  (rfl)

/-- Reindexing `∑ g : G, y.coeff ((σ g)⁻¹ * g)` over right cosets of `Z = σ.fixedPointsSubgroup`
gives `|Z|` copies of the sum over `G ⧸ Z`. -/
private theorem sum_coeff_twisted_eq_card_nsmul (σ : G ≃* G) [Fintype G]
    [Fintype (G ⧸ σ.fixedPointsSubgroup.subtype.range)]
    (y : MonoidAlgebra Λ G) :
    ∑ g : G, y.coeff ((σ g)⁻¹ * g) =
      Nat.card σ.fixedPointsSubgroup •
        ∑ q : G ⧸ σ.fixedPointsSubgroup.subtype.range, y.coeff ((σ q.out⁻¹)⁻¹ * q.out⁻¹) := by
  let Z := σ.fixedPointsSubgroup
  let _ : Fintype Z := Fintype.ofFinite Z
  let eCoset : (G ⧸ Z.subtype.range) × Z ≃ G :=
    (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.inv Z).trans (MonoidHom.ofInjective Z.subtype_injective).toEquiv)).trans
        (Subgroup.groupEquivQuotientProdSubgroup.symm.trans (Equiv.inv G))
  have heCoset : ∀ (q : G ⧸ Z.subtype.range) (z : Z), eCoset (q, z) = (z : G) * q.out⁻¹ := by
    intro q z
    simp [eCoset, Subgroup.groupEquivQuotientProdSubgroup_symm_apply, MonoidHom.ofInjective_apply]
  have hinv : ∀ (q : G ⧸ Z.subtype.range) (z : Z),
      (σ (eCoset (q, z)))⁻¹ * eCoset (q, z) = (σ q.out⁻¹)⁻¹ * q.out⁻¹ := by
    intro q z
    have hz : σ (z : G) = (z : G) := z.2
    rw [heCoset, map_mul, hz, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [← eCoset.sum_comp, Fintype.sum_prod_type_right]
  simp only [hinv, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Z]

/-- **Trace of an automorphism-twisted endomorphism of a finite projective `Λ[G]`-module.** If `G`
is finite, `σ : G ≃* G`, `Z = σ.fixedPointsSubgroup`, and `φ : P →ₗ[Λ] P` satisfies
`φ (single g 1 • p) = single (σ g) 1 • φ p`, then `Tr_Λ(φ, P) = |Z| • Tr_Λ^Z(φ, P)`. -/
theorem hattoriStallingsTrace_of_twistedSMul [Finite G] {σ : G ≃* G} {Z : Subgroup G}
    (hZ : Z = σ.fixedPointsSubgroup) {P : Type*}
    [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite Λ P] [Module.Projective Λ P]
    [Module (MonoidAlgebra Λ Z) P]
    [Module.Finite (MonoidAlgebra Λ Z) P]
    [Module.Projective (MonoidAlgebra Λ Z) P]
    (hP : ∀ (r : MonoidAlgebra Λ Z) (p : P),
      r • p = mapDomainRingHom Λ Z.subtype r • p)
    (φ : Module.End Λ P)
    (φ_Z : Module.End (MonoidAlgebra Λ Z) P)
    (hφ : ∀ (g : G) (p : P), φ (MonoidAlgebra.single g (1 : Λ) • p) =
      MonoidAlgebra.single (σ g) (1 : Λ) • φ p)
    (hφZ : ∀ p, φ_Z p = φ p) :
    hattoriStallingsTrace Λ P φ =
      Nat.card Z • hattoriStallingsGroupTrace Λ Z P φ_Z := by
  subst hZ
  classical
  let Z := σ.fixedPointsSubgroup
  let _ : Fintype G := Fintype.ofFinite G
  have : Finite (G ⧸ Z.subtype.range) := by
    rw [Subgroup.range_subtype]
    infer_instance
  let _ : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
  let ψZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := ψZ.toModule
  obtain ⟨r, π, i, -, -, hπi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let i_Λ : P →ₗ[Λ] Fin r → MonoidAlgebra Λ G := i.restrictScalars Λ
  let π_Λ : (Fin r → MonoidAlgebra Λ G) →ₗ[Λ] P := π.restrictScalars Λ
  have hπi_Λ : π_Λ ∘ₗ i_Λ = .id := by ext p; exact LinearMap.congr_fun hπi p
  let i_Z : P →ₗ[MonoidAlgebra Λ Z] Fin r → MonoidAlgebra Λ G :=
    { toFun := i, map_add' := map_add i,
      map_smul' := fun c p ↦ by rw [RingHom.id_apply, hP, map_smul]; ext k; rfl }
  let π_Z : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ Z] P :=
    { toFun := π, map_add' := map_add π,
      map_smul' := fun c v ↦ by
        have hv : c • v = ψZ c • v := rfl
        rw [RingHom.id_apply, hv, map_smul, hP] }
  have hπi_Z : π_Z ∘ₗ i_Z = .id := by ext p; exact LinearMap.congr_fun hπi p
  let bΛ : Module.Basis ((_ : Fin r) × G) Λ (Fin r → MonoidAlgebra Λ G) :=
    Pi.basis fun _ ↦ MonoidAlgebra.basis G Λ
  let bCoset := TauCeti.MonoidAlgebra.basisCosets Λ Z.subtype Z.subtype_injective
  let bZ : Module.Basis ((_ : Fin r) × (G ⧸ Z.subtype.range)) (MonoidAlgebra Λ Z)
      (Fin r → MonoidAlgebra Λ G) := Pi.basis fun _ ↦ bCoset
  rw [hattoriStallingsTrace_eq_of_retract bΛ i_Λ π_Λ hπi_Λ,
    hattoriStallingsGroupTrace_apply,
    hattoriStallingsTrace_eq_of_retract bZ i_Z π_Z hπi_Z,
    Module.Basis.hattoriStallingsTrace_apply, Module.Basis.hattoriStallingsTrace_apply,
    MonoidAlgebra.cyclicCoeffOne_mkQ, ← map_nsmul]
  congr 1
  simp only [coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma, Finset.smul_sum]
  let T : (Fin r → MonoidAlgebra Λ G) →ₗ[Λ] Fin r → MonoidAlgebra Λ G := i_Λ ∘ₗ φ ∘ₗ π_Λ
  have hT_def : i_Λ ∘ₗ φ ∘ₗ π_Λ = T := rfl
  have hT_smul : ∀ (g : G) (k : Fin r),
      T (MonoidAlgebra.single g (1 : Λ) • Pi.single k 1) k =
        MonoidAlgebra.single (σ g) (1 : Λ) * T (Pi.single k 1) k := by
    intro g k
    have h1 : π_Λ (MonoidAlgebra.single g (1 : Λ) • Pi.single k 1) =
        MonoidAlgebra.single g (1 : Λ) • π_Λ (Pi.single k 1) :=
      map_smul π (MonoidAlgebra.single g (1 : Λ)) (Pi.single k 1)
    have h2 : i_Λ (MonoidAlgebra.single (σ g) (1 : Λ) • φ (π_Λ (Pi.single k 1))) =
        MonoidAlgebra.single (σ g) (1 : Λ) • T (Pi.single k 1) :=
      map_smul i (MonoidAlgebra.single (σ g) (1 : Λ)) (φ (π_Λ (Pi.single k 1)))
    simp only [T, comp_apply, h1, hφ, h2, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hLHS : ∀ g : G,
      (bΛ.repr (T (bΛ ⟨k, g⟩))) ⟨k, g⟩ = (T (Pi.single k 1) k).coeff ((σ g)⁻¹ * g) := by
    intro g
    have hb : bΛ ⟨k, g⟩ = MonoidAlgebra.single g (1 : Λ) • Pi.single k (1 : MonoidAlgebra Λ G) := by
      ext j
      by_cases hjk : j = k
      · subst hjk; simp [bΛ]
      · simp [bΛ, Pi.single_eq_of_ne hjk]
    simp [bΛ, hb, hT_smul]
  have hRHS : ∀ q : G ⧸ Z.subtype.range,
      ((bZ.repr ((i_Z ∘ₗ φ_Z ∘ₗ π_Z) (bZ ⟨k, q⟩))) ⟨k, q⟩).coeff 1 =
        (T (Pi.single k 1) k).coeff ((σ q.out⁻¹)⁻¹ * q.out⁻¹) := by
    intro q
    have hb : bZ ⟨k, q⟩ =
        MonoidAlgebra.single q.out⁻¹ (1 : Λ) • Pi.single k (1 : MonoidAlgebra Λ G) := by
      ext j
      by_cases hjk : j = k
      · subst hjk; simp [bZ, bCoset]
      · simp [bZ, Pi.single_eq_of_ne hjk]
    have hTZ : (i_Z ∘ₗ φ_Z ∘ₗ π_Z) (bZ ⟨k, q⟩) = T (bZ ⟨k, q⟩) := by
      simp [T, i_Z, π_Z, i_Λ, π_Λ, hφZ]
    rw [hTZ, hb]
    simpa [bZ, bCoset, hT_smul] using
      MonoidAlgebra.coeff_one_basisCosets_repr Z
        (MonoidAlgebra.single (σ q.out⁻¹) (1 : Λ) * T (Pi.single k 1) k) q
  simp only [hT_def, hLHS, hRHS, ← Finset.smul_sum]
  exact sum_coeff_twisted_eq_card_nsmul σ (T (Pi.single k 1) k)

end TwistedTrace

end LinearMap

/-! ### Monoid-algebra action on `BalancedExtension` along coefficient ring homomorphisms -/

namespace MonoidAlgebra

/-- Action of a monoid element `n : N` on `Q` as an `R`-linear endomorphism. -/
def elemLinearMap (R : Type*) [Semiring R] {N : Type*} [Monoid N] (Q : Type*) [AddCommMonoid Q]
    [Module R Q] [Module (MonoidAlgebra R N) Q] [IsScalarTower R (MonoidAlgebra R N) Q]
    (n : N) : Q →ₗ[R] Q where
  toFun q := single n (1 : R) • q
  map_add' := smul_add _
  map_smul' c q := by rw [RingHom.id_apply, single_one_smul_comm]

@[simp]
theorem elemLinearMap_apply (R : Type*) [Semiring R] {N : Type*} [Monoid N] (Q : Type*)
    [AddCommMonoid Q] [Module R Q] [Module (MonoidAlgebra R N) Q]
    [IsScalarTower R (MonoidAlgebra R N) Q] (n : N) (q : Q) :
    elemLinearMap R Q n q = single n (1 : R) • q :=
  (rfl)

end MonoidAlgebra

namespace TauCeti.BalancedExtension

section MonoidAlgebra

open _root_.MonoidAlgebra

variable {Λ Λ' : Type*} [Ring Λ] [Ring Λ'] (φ : Λ →+* Λ') (M : Type*) [Monoid M]
  (P : Type*) [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ M) P]
  [IsScalarTower Λ (MonoidAlgebra Λ M) P]

/-- The ring homomorphism `Λ'[M] →+* End_ℤ(Λ' ⊗_Λ P)` combining left multiplication by `Λ'` on the
first factor with the `M`-action on `P`. -/
def monoidAlgebraActionHom :
    MonoidAlgebra Λ' M →+* Module.End ℤ (BalancedExtension φ P) :=
  liftNCRingHom
    { toFun := fun c ↦
        { toFun := fun x ↦ c • x
          map_add' := smul_add c
          map_smul' := fun n x ↦ by rw [RingHom.id_apply, smul_comm n c x] }
      map_one' := LinearMap.ext fun x ↦ one_smul Λ' x
      map_mul' := fun a b ↦ LinearMap.ext fun x ↦ mul_smul a b x
      map_zero' := LinearMap.ext fun x ↦ zero_smul Λ' x
      map_add' := fun a b ↦ LinearMap.ext fun x ↦ add_smul a b x }
    { toFun := fun m ↦ (BalancedExtension.map φ (elemLinearMap Λ P m)).restrictScalars ℤ
      map_one' := LinearMap.ext fun x ↦ by
        have hid : elemLinearMap Λ P (1 : M) = .id := LinearMap.ext fun p ↦ by simp [← one_def]
        simp [hid]
      map_mul' := fun m₁ m₂ ↦ LinearMap.ext fun x ↦ by
        have hmul : elemLinearMap Λ P (m₁ * m₂) =
            elemLinearMap Λ P m₁ ∘ₗ elemLinearMap Λ P m₂ :=
          LinearMap.ext fun p ↦ by simp [← mul_smul, single_mul_single]
        simp [hmul, BalancedExtension.map_comp] }
    fun c m ↦ show Commute _ _ from LinearMap.ext fun x ↦
      (map_smul (BalancedExtension.map φ (elemLinearMap Λ P m)) c x).symm

/-- Scalar extension `Λ' ⊗_Λ P` inherits a left `Λ'[M]`-module structure for any monoid `M` acting
on `P`. -/
instance monoidAlgebraModule : Module (MonoidAlgebra Λ' M) (BalancedExtension φ P) :=
  Module.compHom (BalancedExtension φ P) (monoidAlgebraActionHom φ M P)

@[simp]
theorem monoidAlgebraModule_single_smul_tmul (m : M) (c s : Λ') (p : P) :
    (single m c : MonoidAlgebra Λ' M) • tmul φ s p =
      tmul φ (c * s) (single m (1 : Λ) • p) := by
  have hact : (single m c : MonoidAlgebra Λ' M) • tmul φ s p =
      monoidAlgebraActionHom φ M P (single m c) (tmul φ s p) := rfl
  rw [hact, monoidAlgebraActionHom, liftNCRingHom_single]
  simp [mul_apply_eq_comp]

instance monoidAlgebraIsScalarTower :
    IsScalarTower Λ' (MonoidAlgebra Λ' M) (BalancedExtension φ P) where
  smul_assoc c r x := by
    induction r using induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, add_smul, add_smul, smul_add, ha, hb]
    | single m d =>
      induction x using BalancedExtension.induction_on with
      | tmul s p =>
        rw [smul_single, smul_eq_mul, monoidAlgebraModule_single_smul_tmul,
          monoidAlgebraModule_single_smul_tmul, smul_tmul, mul_assoc]
      | add u v hu hv => rw [smul_add, smul_add, smul_add, hu, hv]

theorem monoidAlgebraModule_comp_mapDomain {N : Type*} [Monoid N] (f : N →* M)
    [Module (MonoidAlgebra Λ N) P] [IsScalarTower Λ (MonoidAlgebra Λ N) P]
    (hPN : ∀ (r : MonoidAlgebra Λ N) (p : P), r • p = mapDomainRingHom Λ f r • p)
    (r : MonoidAlgebra Λ' N) (x : BalancedExtension φ P) :
    r • x = mapDomainRingHom Λ' f r • x := by
  induction r using induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, _root_.map_add, add_smul, ha, hb]
  | single n c =>
    induction x using BalancedExtension.induction_on with
    | tmul s p =>
      simp only [mapDomainRingHom_apply, mapDomain_single, monoidAlgebraModule_single_smul_tmul]
      rw [hPN (single n (1 : Λ)) p]
      simp
    | add u v hu hv => rw [smul_add, smul_add, hu, hv]

/-- `BalancedExtension (mapRingHom M φ) P` (`Λ'[M] ⊗_{Λ[M]} P`) identifies `Λ'[M]`-linearly with
`BalancedExtension φ P` (`Λ' ⊗_Λ P`). -/
def monoidAlgebraEquiv :
    BalancedExtension (mapRingHom M φ) P ≃ₗ[MonoidAlgebra Λ' M] BalancedExtension φ P := by
  let Φ := mapRingHom M φ
  let g : P →ₛₗ[Φ] BalancedExtension φ P :=
    { toFun := fun p ↦ tmul φ 1 p
      map_add' := tmul_add 1
      map_smul' := fun r p ↦ by
        induction r using induction_linear with
        | zero => simp
        | add x y hx hy => rw [add_smul, tmul_add, _root_.map_add, add_smul, hx, hy]
        | single m c =>
          simp only [Φ, mapRingHom_single]
          rw [single_smul_eq_smul_single_one_smul, tmul_smul, one_mul,
            monoidAlgebraModule_single_smul_tmul, mul_one] }
  let modΛ' : Module Λ' (BalancedExtension Φ P) :=
    Module.compHom (BalancedExtension Φ P) (singleOneRingHom : Λ' →+* MonoidAlgebra Λ' M)
  have hmodΛ' : ∀ (d : Λ') (x : BalancedExtension Φ P),
      @HSMul.hSMul _ _ _ (@instHSMul _ _ modΛ'.toSMul) d x =
        (single (1 : M) d : MonoidAlgebra Λ' M) • x :=
    fun _ _ ↦ rfl
  let h : @LinearMap Λ Λ' _ _ φ P (BalancedExtension Φ P) _ _ _ modΛ' :=
    @LinearMap.mk Λ Λ' _ _ φ P (BalancedExtension Φ P) _ _ _ modΛ'
      ⟨fun p ↦ tmul Φ 1 p, tmul_add 1⟩
      fun c p ↦ by
        dsimp only
        have hc : c • p = (single (1 : M) c : MonoidAlgebra Λ M) • p := by
          rw [← smul_one_smul (MonoidAlgebra Λ M) c p, one_def, smul_single, smul_eq_mul, mul_one]
        rw [hmodΛ', hc, tmul_smul, one_mul, smul_tmul, mul_one]
        simp [Φ]
  let invΛ' : @LinearMap Λ' Λ' _ _ (.id Λ') (BalancedExtension φ P) (BalancedExtension Φ P)
      _ _ _ modΛ' := @BalancedExtension.lift Λ Λ' _ _ φ P _ _ (BalancedExtension Φ P) _ modΛ' h
  have hinv_tmul : ∀ (s : Λ') (p : P), invΛ' (tmul φ s p) = tmul Φ (single 1 s) p := by
    intro s p
    have hl := @BalancedExtension.lift_tmul Λ Λ' _ _ φ P _ _ (BalancedExtension Φ P) _ modΛ' h s p
    have hh : h p = tmul Φ 1 p := rfl
    rw [hl, hmodΛ', hh, smul_tmul, mul_one]
  let invM : BalancedExtension φ P →ₗ[MonoidAlgebra Λ' M] BalancedExtension Φ P :=
    { toFun := invΛ'
      map_add' := _root_.map_add invΛ'
      map_smul' := fun r x ↦ by
        rw [RingHom.id_apply]
        induction r using induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_smul, _root_.map_add, add_smul, ha, hb]
        | single m c =>
          induction x using BalancedExtension.induction_on with
          | tmul s p =>
            rw [monoidAlgebraModule_single_smul_tmul, hinv_tmul, hinv_tmul, tmul_smul,
              smul_tmul]
            simp [Φ, single_mul_single]
          | add u v hu hv =>
            rw [smul_add, _root_.map_add, _root_.map_add, smul_add, hu, hv] }
  refine LinearEquiv.ofLinearMap (BalancedExtension.lift g) invM ?_
    (BalancedExtension.hom_ext fun p ↦ by simp [invM, g, hinv_tmul, ← one_def, Φ])
  refine LinearMap.ext fun x ↦ ?_
  induction x using BalancedExtension.induction_on with
  | tmul s p =>
    simp only [LinearMap.comp_apply, LinearMap.id_apply, invM, LinearMap.coe_mk, AddHom.coe_mk,
      hinv_tmul, Φ, lift_tmul, g, monoidAlgebraModule_single_smul_tmul, mul_one]
    have hp : single (1 : M) (1 : Λ) • p = p := by rw [← one_def, one_smul]
    rw [hp]
  | add u v hu hv => simp only [_root_.map_add, LinearMap.id_apply] at hu hv ⊢; rw [hu, hv]

@[simp]
theorem monoidAlgebraEquiv_tmul_one (p : P) :
    monoidAlgebraEquiv φ M P (tmul (mapRingHom M φ) 1 p) = tmul φ 1 p := by
  simp [monoidAlgebraEquiv]

@[simp]
theorem monoidAlgebraEquiv_symm_tmul (s : Λ') (p : P) :
    (monoidAlgebraEquiv φ M P).symm (tmul φ s p) =
      tmul (mapRingHom M φ) (single 1 s) p := by
  rw [tmul_eq_smul_one_tmul (f := φ) s p, ← monoidAlgebraEquiv_tmul_one φ M P p]
  have hs : s • monoidAlgebraEquiv φ M P (tmul (mapRingHom M φ) 1 p) =
      (single (1 : M) s : MonoidAlgebra Λ' M) •
        monoidAlgebraEquiv φ M P (tmul (mapRingHom M φ) 1 p) := by
    rw [monoidAlgebraEquiv_tmul_one, monoidAlgebraModule_single_smul_tmul, smul_tmul]
    have hp : single (1 : M) (1 : Λ) • p = p := by rw [← one_def, one_smul]
    rw [hp]
  rw [hs, (monoidAlgebraEquiv φ M P).symm.map_smul, LinearEquiv.symm_apply_apply, smul_tmul,
    mul_one]

instance monoidAlgebraFinite [Module.Finite (MonoidAlgebra Λ M) P] :
    Module.Finite (MonoidAlgebra Λ' M) (BalancedExtension φ P) :=
  Module.Finite.equiv (monoidAlgebraEquiv φ M P)

instance monoidAlgebraProjective [Module.Projective (MonoidAlgebra Λ M) P] :
    Module.Projective (MonoidAlgebra Λ' M) (BalancedExtension φ P) :=
  Module.Projective.of_equiv (monoidAlgebraEquiv φ M P)

end MonoidAlgebra

end TauCeti.BalancedExtension

/-! ### Monoid extensions `1 → G → Γtilde → ℤ → 1` and Stacks Section 64.15 -/

namespace TauCeti.MonoidExtension

open _root_.MonoidAlgebra

section Structure

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

/-- The submonoid `Γ = deg⁻¹(ℕ) = { γ : Γtilde | 0 ≤ toAdd (deg γ) }` of elements of nonnegative
degree in `Γtilde`. -/
def nonnegSubmonoid (deg : Γtilde →* Multiplicative ℤ) : Submonoid Γtilde where
  carrier := { γ : Γtilde | 0 ≤ Multiplicative.toAdd (deg γ) }
  one_mem' := by simp
  mul_mem' ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul] at ha hb ⊢
    omega

@[simp]
theorem mem_nonnegSubmonoid {deg : Γtilde →* Multiplicative ℤ} {γ : Γtilde} :
    γ ∈ nonnegSubmonoid deg ↔ 0 ≤ Multiplicative.toAdd (deg γ) :=
  Iff.rfl

/-- Inclusion of the kernel subgroup `G` into `nonnegSubmonoid deg`. -/
def toNonnegSubmonoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) : G →* nonnegSubmonoid deg where
  toFun g := ⟨ι g, by
    have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
    rw [MonoidHom.mem_ker] at hg
    simp [hg]⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' a b := Subtype.ext (map_mul ι a b)

@[simp]
theorem coe_toNonnegSubmonoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (g : G) :
    (toNonnegSubmonoid ι deg hker g : Γtilde) = ι g :=
  (rfl)

theorem toNonnegSubmonoid_injective {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) :
    Function.Injective (toNonnegSubmonoid ι deg hker) :=
  fun _ _ h ↦ hι (congrArg Subtype.val h)

private theorem conj_mem_range (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (γ : Γtilde) (g : G) :
    γ * ι g * γ⁻¹ ∈ ι.range := by
  rw [hker, MonoidHom.mem_ker]
  have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
  rw [MonoidHom.mem_ker] at hg
  simp [hg]

/-- Conjugation by `γ : Γtilde` on `G` across `1 → G → Γtilde → ℤ`. -/
def conjAut (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) : G ≃* G where
  toFun g := (conj_mem_range ι deg hker γ g).choose
  invFun g := (conj_mem_range ι deg hker γ⁻¹ g).choose
  left_inv g := hι <| by
    rw [(conj_mem_range ι deg hker γ⁻¹ _).choose_spec,
      (conj_mem_range ι deg hker γ g).choose_spec]
    group
  right_inv g := hι <| by
    rw [(conj_mem_range ι deg hker γ _).choose_spec,
      (conj_mem_range ι deg hker γ⁻¹ g).choose_spec]
    group
  map_mul' a b := hι <| by
    rw [(conj_mem_range ι deg hker γ (a * b)).choose_spec, map_mul, map_mul,
      (conj_mem_range ι deg hker γ a).choose_spec,
      (conj_mem_range ι deg hker γ b).choose_spec]
    group

@[simp]
theorem ι_conjAut_apply (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) (g : G) :
    ι (conjAut ι deg hι hker γ g) = γ * ι g * γ⁻¹ :=
  (conj_mem_range ι deg hker γ g).choose_spec

@[simp]
theorem conjAut_symm (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) :
    (conjAut ι deg hι hker γ).symm = conjAut ι deg hι hker γ⁻¹ := by
  ext g
  apply (conjAut ι deg hι hker γ).injective
  apply hι
  simp
  group

/-- The centralizer subgroup `Z_γ = { g ∈ G | ι g * γ = γ * ι g } ≤ G`. -/
def centralizerSubgroup (ι : G →* Γtilde) (γ : Γtilde) : Subgroup G :=
  (Subgroup.centralizer {γ}).comap ι

@[simp]
theorem mem_centralizerSubgroup {ι : G →* Γtilde} {γ : Γtilde} {g : G} :
    g ∈ centralizerSubgroup ι γ ↔ ι g * γ = γ * ι g :=
  Subgroup.mem_centralizer_singleton_iff

theorem commute_toNonnegSubmonoid_of_mem_centralizerSubgroup
    (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
    (γ : nonnegSubmonoid deg) (z : centralizerSubgroup ι γ.1) :
    Commute ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.1).subtype z) γ := by
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, coe_toNonnegSubmonoid]
  exact mem_centralizerSubgroup.1 z.2

/-- Fixed points of `conjAut` on `G` are precisely `centralizerSubgroup ι γ`. -/
theorem fixedPointsSubgroup_conjAut (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) :
    (conjAut ι deg hι hker γ).fixedPointsSubgroup = centralizerSubgroup ι γ := by
  ext g
  rw [MulEquiv.mem_fixedPointsSubgroup, ← hι.eq_iff, ι_conjAut_apply,
    mul_inv_eq_iff_eq_mul, mem_centralizerSubgroup, eq_comm]

/-- Conjugation of `γ : nonnegSubmonoid deg` by `k : G` preserves `nonnegSubmonoid deg`. -/
def conjNonneg (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (k : G) (γ : nonnegSubmonoid deg) : nonnegSubmonoid deg :=
  ⟨ι k * γ.1 * (ι k)⁻¹, by
    have hγ : 0 ≤ Multiplicative.toAdd (deg γ.1) := γ.2
    have hk : ι k ∈ deg.ker := hker ▸ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker] at hk
    simpa [hk] using hγ⟩

@[simp]
theorem coe_conjNonneg (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (k : G) (γ : nonnegSubmonoid deg) :
    (conjNonneg ι deg hker k γ : Γtilde) = ι k * γ.1 * (ι k)⁻¹ :=
  (rfl)

/-- Conjugation by `k : G` identifies `Z_γ` with `Z_{k γ k⁻¹}`. -/
def conjCentralizerEquiv (ι : G →* Γtilde) (k : G) (γ : Γtilde) :
    centralizerSubgroup ι γ ≃* centralizerSubgroup ι (ι k * γ * (ι k)⁻¹) where
  toFun z := ⟨k * z.1 * k⁻¹, by
    have hz : ι z.1 * γ = γ * ι z.1 := mem_centralizerSubgroup.1 z.2
    rw [mem_centralizerSubgroup]
    calc
      ι (k * z.1 * k⁻¹) * (ι k * γ * (ι k)⁻¹)
          = ι k * (ι z.1 * γ) * (ι k)⁻¹ := by simp [mul_assoc]
      _ = ι k * (γ * ι z.1) * (ι k)⁻¹ := by rw [hz]
      _ = (ι k * γ * (ι k)⁻¹) * ι (k * z.1 * k⁻¹) := by simp [mul_assoc]⟩
  invFun z' := ⟨k⁻¹ * z'.1 * k, by
    have hz' : ι z'.1 * (ι k * γ * (ι k)⁻¹) = (ι k * γ * (ι k)⁻¹) * ι z'.1 :=
      mem_centralizerSubgroup.1 z'.2
    rw [mem_centralizerSubgroup]
    have h1 := congrArg (fun x ↦ (ι k)⁻¹ * x * ι k) hz'
    simpa [mul_assoc] using h1⟩
  left_inv z := Subtype.ext (by group)
  right_inv z' := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- On any `Λ[Γ]`-module `P` with compatible `Λ[G]`-action, `elemLinearMap Λ P γ` twists the
`G`-action by `conjAut`. -/
theorem elemLinearMap_single_smul {Λ : Type*} [Ring Λ]
    {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) {hker : ι.range = deg.ker}
    {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) (g : G) (p : P) :
    elemLinearMap Λ P γ ((single g (1 : Λ) : MonoidAlgebra Λ G) • p) =
      (single (conjAut ι deg hι hker γ.1 g) (1 : Λ) : MonoidAlgebra Λ G) •
        elemLinearMap Λ P γ p := by
  rw [elemLinearMap_apply, elemLinearMap_apply, hPG, hPG]
  simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
  have hrel : γ * toNonnegSubmonoid ι deg hker g =
      toNonnegSubmonoid ι deg hker (conjAut ι deg hι hker γ.1 g) * γ := by
    ext
    simp [mul_assoc]
  rw [hrel]

end Structure

/-! ### Centralizer group-ring traces and Lemma 64.15.4 -/

section CentralizerTrace

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ P]
  [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
  [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
  [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]

/-- **The centralizer group-ring trace** `Tr_Λ^{Z_γ}(γ, P) ∈ Λ / [Λ, Λ]` of `γ ∈ Γ` on `P`,
restricted to `Z_γ = centralizerSubgroup ι γ.1`. -/
def centralizerGroupTrace
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) : TauCeti.cyclicQuotient ℤ Λ :=
  let Z := centralizerSubgroup ι γ.1
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  have hsub := Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z
    (fun _ _ ↦ rfl) P (fun _ _ ↦ rfl)
  have _ := hsub.2.2.2.1
  have _ := hsub.2.2.2.2
  let ιZ : Z →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z.subtype
  have hactZ : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = mapDomain ιZ r • p := fun r p ↦ by
    have hcomp : r • p = φZ r • p := rfl
    rw [hcomp, hPG]
    simp [φZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
  LinearMap.hattoriStallingsGroupTrace Λ Z P
    (ιZ.singleSMulLinearMap
      (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ) P hactZ)

variable {Λ ι deg hker}

/-- Agreement of `centralizerGroupTrace` with `hattoriStallingsGroupTrace` whenever `P` already
carries a compatible `Λ[Z_γ]`-module structure. -/
theorem centralizerGroupTrace_eq_hattoriStallingsGroupTrace
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg)
    [instZ : Module (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    [hfin : Module.Finite (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    [hproj : Module.Projective (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    (hPZ : ∀ (r : MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p)
    (u_Z : Module.End (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P)
    (huZ : ∀ p, u_Z p = single γ (1 : Λ) • p) :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      LinearMap.hattoriStallingsGroupTrace Λ (centralizerSubgroup ι γ.1) P u_Z := by
  let Z := centralizerSubgroup ι γ.1
  let φZ := mapDomainRingHom Λ Z.subtype
  have hinst : instZ = Module.compHom P φZ := Module.ext' _ _ hPZ
  subst hinst
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  rw [centralizerGroupTrace]
  congr 1
  refine LinearMap.ext fun p ↦ ?_
  rw [MonoidHom.singleSMulLinearMap_apply, huZ]

/-- **Monoid-extension trace identity** (Stacks Project, Section 64.15, Lemma 64.15.4). For any
`γ ∈ Γ`, the `Λ`-trace of `γ` on `P` equals `|Z_γ|` times its centralizer group-ring trace:
`Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul
    (hι : Function.Injective ι)
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module.Finite Λ P] [Module.Projective Λ P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    LinearMap.hattoriStallingsTrace Λ P (elemLinearMap Λ P γ) =
      Nat.card (centralizerSubgroup ι γ.1) • centralizerGroupTrace Λ ι deg hker hPG γ := by
  let σ := conjAut ι deg hι hker γ.1
  let Z := centralizerSubgroup ι γ.1
  have hZ : Z = σ.fixedPointsSubgroup := (fixedPointsSubgroup_conjAut ι deg hι hker γ.1).symm
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  have hφ : ∀ (g : G) (p : P), elemLinearMap Λ P γ (single g (1 : Λ) • p) =
      single (σ g) (1 : Λ) • elemLinearMap Λ P γ p :=
    elemLinearMap_single_smul hι hPG γ
  let φ_Z := LinearMap.restrictFixedSubgroup hZ.le (fun _ _ ↦ rfl)
    (elemLinearMap Λ P γ) hφ
  rw [LinearMap.hattoriStallingsTrace_of_twistedSMul hZ (fun _ _ ↦ rfl)
    (elemLinearMap Λ P γ) φ_Z hφ (fun _ ↦ rfl),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) φ_Z (fun _ ↦ rfl)]

/-- **`G`-conjugation invariance of `centralizerGroupTrace`.** Conjugating `γ ∈ Γ` by any `k ∈ G`
preserves `Tr_Λ^{Z_γ}(γ, P)`. -/
theorem centralizerGroupTrace_conjNonneg
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (k : G) (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ ι deg hker hPG (conjNonneg ι deg hker k γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ := by
  let γ' := conjNonneg ι deg hker k γ
  let Z := centralizerSubgroup ι γ.1
  let Z' := centralizerSubgroup ι γ'.1
  let φZ := mapDomainRingHom Λ Z.subtype
  let φZ' := mapDomainRingHom Λ Z'.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  let _ : Module (MonoidAlgebra Λ Z') (MonoidAlgebra Λ G) := φZ'.toModule
  let _ : Module (MonoidAlgebra Λ Z') P := Module.compHom P φZ'
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  obtain ⟨_, _, _, hfinZ', hprojZ'⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z' (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let ιZ : Z →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z.subtype
  let ιZ' : Z' →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z'.subtype
  have hactZ : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = mapDomain ιZ r • p := fun r p ↦ by
    have hcomp : r • p = φZ r • p := rfl
    rw [hcomp, hPG]
    simp [φZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
  have hactZ' : ∀ (r : MonoidAlgebra Λ Z') (p : P), r • p = mapDomain ιZ' r • p := fun r p ↦ by
    have hcomp : r • p = φZ' r • p := rfl
    rw [hcomp, hPG]
    simp [φZ', ιZ', mapDomainRingHom_apply, mapDomain_mapDomain]
  let uZ := ιZ.singleSMulLinearMap
    (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ) P hactZ
  let uZ' := ιZ'.singleSMulLinearMap
    (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ') P hactZ'
  let eZ : Z ≃* Z' := conjCentralizerEquiv ι k γ.1
  let E : MonoidAlgebra Λ Z ≃+* MonoidAlgebra Λ Z' := mapDomainRingEquiv Λ eZ
  let _ := RingHomInvPair.of_ringEquiv E
  let _ := RingHomInvPair.of_ringEquiv_symm E
  have hcompZ : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = φZ r • p := fun _ _ ↦ rfl
  have hcompZ' : ∀ (r : MonoidAlgebra Λ Z') (p : P), r • p = φZ' r • p := fun _ _ ↦ rfl
  let j : P ≃ₛₗ[(E : MonoidAlgebra Λ Z →+* MonoidAlgebra Λ Z')] P :=
    { toFun := fun p ↦ (single k (1 : Λ) : MonoidAlgebra Λ G) • p
      invFun := fun p ↦ (single k⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • p
      left_inv := fun p ↦ by simp [← mul_smul, single_mul_single, ← one_def]
      right_inv := fun p ↦ by simp [← mul_smul, single_mul_single, ← one_def]
      map_add' := fun a b ↦ smul_add _ a b
      map_smul' := fun r p ↦ by
        induction r using induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_smul, smul_add, _root_.map_add, add_smul, ha, hb]
        | single z c =>
          rw [hcompZ, hcompZ']
          have hE : (E : MonoidAlgebra Λ Z →+* MonoidAlgebra Λ Z') (single z c) =
              single (eZ z) c := by
            simp [E]
          rw [hE]
          simp only [φZ, φZ', mapDomainRingHom_apply, mapDomain_single, Subgroup.coe_subtype,
            ← mul_smul, single_mul_single, one_mul, mul_one]
          have hgrp : k * (z : G) = (eZ z : G) * k := by
            have heZ : (eZ z : G) = k * (z : G) * k⁻¹ := rfl
            rw [heZ]
            group
          rw [hgrp] }
  have hinter : ∀ p : P, uZ' (j p) = j (uZ p) := by
    intro p
    simp only [uZ, uZ', j, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      MonoidHom.singleSMulLinearMap_apply, hPG, mapDomainRingHom_apply, mapDomain_single,
      ← mul_smul, single_mul_single, one_mul]
    have hγ : γ' * toNonnegSubmonoid ι deg hker k =
        toNonnegSubmonoid ι deg hker k * γ := by
      ext
      simp [γ', mul_assoc]
    rw [hγ]
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ' (fun _ _ ↦ rfl) uZ'
    (by simp [uZ']),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ (by simp [uZ])]
  have hE_hom : (E : MonoidAlgebra Λ Z →+* MonoidAlgebra Λ Z') =
      mapDomainRingHom Λ eZ.toMonoidHom := toRingHom_mapDomainRingEquiv eZ
  exact j.hattoriStallingsGroupTrace_eq_of_semilinear eZ hE_hom hinter

end CentralizerTrace

/-! ### `G`-coinvariants and Lemma 64.15.5 -/

section Coinvariants

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
  (hι : Function.Injective ι) (hker : ι.range = deg.ker)

/-- The fiber `{ γ ∈ Γ | deg γ = ofAdd d }` of elements of degree `d : ℕ` in
`nonnegSubmonoid deg`. -/
@[ext]
structure DegreeFiber (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) where
  /-- Underlying element of `nonnegSubmonoid deg`. -/
  val : nonnegSubmonoid deg
  /-- Degree condition `deg val.1 = Multiplicative.ofAdd d`. -/
  deg_eq : deg val.1 = Multiplicative.ofAdd (d : ℤ)

namespace DegreeFiber

/-- Conjugation of an element of `DegreeFiber deg d` by `k : G`. -/
def conj {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} (hker : ι.range = deg.ker)
    {d : ℕ} (k : G) (γ : DegreeFiber deg d) : DegreeFiber deg d :=
  ⟨conjNonneg ι deg hker k γ.val, by
    have hk : ι k ∈ deg.ker := hker ▸ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker] at hk
    simpa [conjNonneg, hk] using γ.deg_eq⟩

@[simp]
theorem val_conj {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} (hker : ι.range = deg.ker)
    {d : ℕ} (k : G) (γ : DegreeFiber deg d) :
    (conj hker k γ).val = conjNonneg ι deg hker k γ.val :=
  (rfl)

theorem finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (DegreeFiber deg d) := by
  by_cases hne : Nonempty (DegreeFiber deg d)
  · obtain ⟨γ₀⟩ := hne
    let f : G → DegreeFiber deg d := fun g ↦
      ⟨toNonnegSubmonoid ι deg hker g * γ₀.val, by
        have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
        rw [MonoidHom.mem_ker] at hg
        simpa [hg] using γ₀.deg_eq⟩
    refine Finite.of_surjective f fun γ ↦ ?_
    have hmem : γ.val.1 * γ₀.val.1⁻¹ ∈ ι.range := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ.deg_eq, γ₀.deg_eq, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    ext1; ext1
    rw [Submonoid.coe_mul, coe_toNonnegSubmonoid, hg, inv_mul_cancel_right]
  · have : IsEmpty (DegreeFiber deg d) := not_nonempty_iff.1 hne
    infer_instance

end DegreeFiber

/-- Equivalence relation of `G`-conjugacy on `DegreeFiber deg d`. -/
def conjSetoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    Setoid (DegreeFiber deg d) where
  r γ₁ γ₂ := ∃ k : G, γ₁.val.1 = ι k * γ₂.val.1 * (ι k)⁻¹
  iseqv :=
    { refl := fun γ ↦ ⟨1, by simp⟩
      symm := fun ⟨k, hk⟩ ↦ ⟨k⁻¹, by rw [hk, map_inv]; group⟩
      trans := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ↦ ⟨k₁ * k₂, by rw [hk₁, hk₂]; simp [mul_assoc]⟩ }

theorem conjSetoid_rel {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} {d : ℕ}
    {γ₁ γ₂ : DegreeFiber deg d} :
    (conjSetoid ι deg d) γ₁ γ₂ ↔ ∃ k : G, γ₁.val.1 = ι k * γ₂.val.1 * (ι k)⁻¹ := by
  rfl

/-- `G`-conjugacy classes of degree-`d` elements in `nonnegSubmonoid deg`. -/
abbrev ConjClasses (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) : Type _ :=
  Quotient (conjSetoid ι deg d)

theorem ConjClasses.finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (ConjClasses ι deg d) := by
  have := DegreeFiber.finite ι hker d
  exact Quotient.finite (conjSetoid ι deg d)

/-- The `Λ`-linear endomorphism of `Coinvariants Λ G P` induced by `γ₀ ∈ Γ`. -/
def coinvariantEnd {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ₀ : nonnegSubmonoid deg) :
    Module.End Λ (Coinvariants Λ G P) :=
  Coinvariants.desc ((Coinvariants.mk Λ G P).comp (elemLinearMap Λ P γ₀)) fun g p ↦ by
    simp only [LinearMap.comp_apply]
    rw [elemLinearMap_single_smul hι hPG γ₀ g p, Coinvariants.mk_single_one_smul]

@[simp]
theorem coinvariantEnd_mk {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ₀ : nonnegSubmonoid deg) (p : P) :
    coinvariantEnd Λ ι deg hι hker hPG γ₀ (Coinvariants.mk Λ G P p) =
      Coinvariants.mk Λ G P (single γ₀ (1 : Λ) • p) := by
  simp [coinvariantEnd]

/-- Elements of `Γ` of the same degree induce the same endomorphism on `Coinvariants Λ G P`
(so the induced action of `1 ∈ ℕ` on `P_G` is independent of the chosen lift `γ₀ ∈ deg⁻¹(1)`). -/
theorem coinvariantEnd_eq_of_deg_eq {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {γ₁ γ₀ : nonnegSubmonoid deg} (hdeg : deg γ₁.1 = deg γ₀.1) :
    coinvariantEnd Λ ι deg hι hker hPG γ₁ = coinvariantEnd Λ ι deg hι hker hPG γ₀ := by
  ext p
  simp only [coinvariantEnd_mk]
  have hmem : γ₁.1 * γ₀.1⁻¹ ∈ ι.range := by
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv, hdeg, mul_inv_cancel]
  obtain ⟨g, hg⟩ := hmem
  have hγ₁ : γ₁ = toNonnegSubmonoid ι deg hker g * γ₀ := by
    ext
    rw [Submonoid.coe_mul, coe_toNonnegSubmonoid, hg, inv_mul_cancel_right]
  have hsmul : single γ₁ (1 : Λ) • p =
      (single g (1 : Λ) : MonoidAlgebra Λ G) • (single γ₀ (1 : Λ) • p) := by
    rw [hPG, mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul, hγ₁]
  rw [hsmul, Coinvariants.mk_single_one_smul]

/-- The centralizer group-ring trace descended to `G`-conjugacy classes in `DegreeFiber deg d`. -/
def conjClassGroupTrace [Finite G] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (d : ℕ) :
    ConjClasses ι deg d → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ ↦ centralizerGroupTrace Λ ι deg hker hPG γ.val) fun a b ⟨k, hk⟩ ↦ by
    have ha : a.val = conjNonneg ι deg hker k b.val := Subtype.ext hk
    rw [ha]
    exact centralizerGroupTrace_conjNonneg hPG k b.val

@[simp]
theorem conjClassGroupTrace_mk [Finite G] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassGroupTrace Λ ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ.val :=
  (rfl)

section OrbitBijection

/-- Given a basepoint `γ₀ : DegreeFiber deg d`, `DegreeFiber deg d` identifies with `G` via the
unique `g : G` satisfying `ι g * γ.val.1 = γ₀.val.1`. -/
private def degreeFiberEquivGroup {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) (hker : ι.range = deg.ker)
    {d : ℕ} (γ₀ : DegreeFiber deg d) :
    DegreeFiber deg d ≃ G where
  toFun γ :=
    (show γ₀.val.1 * γ.val.1⁻¹ ∈ ι.range by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ₀.deg_eq, γ.deg_eq, mul_inv_cancel]).choose
  invFun g :=
    ⟨(toNonnegSubmonoid ι deg hker g⁻¹) * γ₀.val, by
      have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
      rw [MonoidHom.mem_ker] at hg
      simpa [hg] using γ₀.deg_eq⟩
  left_inv γ := by
    ext1; ext1
    have hspec :=
      (show γ₀.val.1 * γ.val.1⁻¹ ∈ ι.range by
        rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ₀.deg_eq, γ.deg_eq,
          mul_inv_cancel]).choose_spec
    simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv, hspec]
    group
  right_inv g := hι <| by
    have hspec :=
      (show γ₀.val.1 * ((toNonnegSubmonoid ι deg hker g⁻¹ * γ₀.val : nonnegSubmonoid deg) :
          Γtilde)⁻¹ ∈ ι.range by
        rw [hker, MonoidHom.mem_ker, map_mul, map_inv]
        have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
        rw [MonoidHom.mem_ker] at hg
        simp [hg]).choose_spec
    rw [hspec]
    simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv]
    group

private theorem ι_degreeFiberEquivGroup_mul {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) (hker : ι.range = deg.ker)
    {d : ℕ} (γ₀ γ : DegreeFiber deg d) :
    ι (degreeFiberEquivGroup hι hker γ₀ γ) * γ.val.1 = γ₀.val.1 := by
  have hspec :=
    (show γ₀.val.1 * γ.val.1⁻¹ ∈ ι.range by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ₀.deg_eq, γ.deg_eq,
        mul_inv_cancel]).choose_spec
  have hdef : degreeFiberEquivGroup hι hker γ₀ γ =
      (show γ₀.val.1 * γ.val.1⁻¹ ∈ ι.range by
        rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ₀.deg_eq, γ.deg_eq,
          mul_inv_cancel]).choose := rfl
  rw [hdef, hspec, inv_mul_cancel_right]

/-- Each `G`-conjugacy orbit fiber over `c` identifies with `G ⧸ Z_{c.out}`. -/
private def orbitCosetEquiv {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) {d : ℕ} (c : ConjClasses ι deg d) :
    G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range ≃
      { x : DegreeFiber deg d // Quotient.mk (conjSetoid ι deg d) x = c } :=
  Equiv.ofBijective
    (fun q ↦ ⟨DegreeFiber.conj hker q.out c.out, by
      have hrel : (conjSetoid ι deg d) (DegreeFiber.conj hker q.out c.out) c.out :=
        ⟨q.out, rfl⟩
      exact (Quotient.sound hrel).trans (Quotient.out_eq c)⟩)
    ⟨fun q₁ q₂ h ↦ by
      have hsmul : DegreeFiber.conj hker q₁.out c.out = DegreeFiber.conj hker q₂.out c.out :=
        congrArg Subtype.val h
      have hval : ι q₁.out * c.out.val.1 * (ι q₁.out)⁻¹ =
          ι q₂.out * c.out.val.1 * (ι q₂.out)⁻¹ :=
        congrArg Subtype.val (congrArg DegreeFiber.val hsmul)
      have hcomm : ι (q₁.out⁻¹ * q₂.out) * c.out.val.1 = c.out.val.1 * ι (q₁.out⁻¹ * q₂.out) := by
        calc
          ι (q₁.out⁻¹ * q₂.out) * c.out.val.1
              = (ι q₁.out)⁻¹ * (ι q₂.out * c.out.val.1 * (ι q₂.out)⁻¹) * ι q₂.out := by
                simp [mul_assoc]
          _ = (ι q₁.out)⁻¹ * (ι q₁.out * c.out.val.1 * (ι q₁.out)⁻¹) * ι q₂.out := by
                rw [← hval]
          _ = c.out.val.1 * ι (q₁.out⁻¹ * q₂.out) := by simp [mul_assoc]
      have hmem : q₁.out⁻¹ * q₂.out ∈ (centralizerSubgroup ι c.out.val.1).subtype.range :=
        ⟨⟨q₁.out⁻¹ * q₂.out, mem_centralizerSubgroup.2 hcomm⟩, rfl⟩
      have hmk := (QuotientGroup.eq).2 hmem
      simpa [Quotient.out_eq] using hmk,
    fun ⟨x, hx⟩ ↦ by
      have hx' : Quotient.mk (conjSetoid ι deg d) x =
          Quotient.mk (conjSetoid ι deg d) c.out := hx.trans (Quotient.out_eq c).symm
      obtain ⟨g, hgx⟩ := Quotient.exact hx'
      let q : G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range := QuotientGroup.mk g
      have hq : q.out⁻¹ * g ∈ (centralizerSubgroup ι c.out.val.1).subtype.range := by
        have hmk : QuotientGroup.mk (s := (centralizerSubgroup ι c.out.val.1).subtype.range)
            q.out = QuotientGroup.mk g := Quotient.out_eq q
        exact (QuotientGroup.eq).1 hmk
      obtain ⟨z, hz⟩ := hq
      refine ⟨q, Subtype.ext <| DegreeFiber.ext <| Subtype.ext ?_⟩
      have hzc : ι (z : G) * c.out.val.1 = c.out.val.1 * ι (z : G) :=
        mem_centralizerSubgroup.1 z.2
      have hg : g = q.out * (z : G) := eq_mul_of_inv_mul_eq hz.symm
      simp only [DegreeFiber.val_conj, coe_conjNonneg, hgx, hg, map_mul, mul_inv_rev]
      calc
        ι q.out * c.out.val.1 * (ι q.out)⁻¹
            = ι q.out * (c.out.val.1 * ι (z : G) * (ι (z : G))⁻¹) * (ι q.out)⁻¹ := by simp
        _ = ι q.out * (ι (z : G) * c.out.val.1 * (ι (z : G))⁻¹) * (ι q.out)⁻¹ := by
              rw [← hzc]
        _ = ι q.out * ι (z : G) * c.out.val.1 * ((ι (z : G))⁻¹ * (ι q.out)⁻¹) := by
              simp [mul_assoc]⟩

end OrbitBijection

variable {Λ ι deg hι hker}

/-- **Coinvariant trace over `G`-conjugacy classes** (Stacks Project, Section 64.15,
Lemma 64.15.5). For any `d : ℕ` (in particular `d = 1`) and any `γ₀ ∈ Γ` of degree `d`, the
`Λ`-trace of `γ₀` on the `G`-coinvariant module `P_G` equals the sum over `G`-conjugacy classes in
`deg⁻¹(d)` of the centralizer group-ring traces `Tr_Λ^{Z_γ}(γ, P)`:
`Tr_Λ(γ₀, P_G) = ∑_{[γ] ∈ deg⁻¹(d) / G} Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses [Finite G]
    {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} [Fintype (ConjClasses ι deg d)]
    (γ₀ : DegreeFiber deg d) :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P)
        (coinvariantEnd Λ ι deg hι hker hPG γ₀.val) =
      ∑ c : ConjClasses ι deg d,
        conjClassGroupTrace Λ ι deg hker hPG d c := by
  classical
  let F := DegreeFiber deg d
  let R_orb := conjSetoid ι deg d
  have : Finite F := DegreeFiber.finite ι hker d
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨r, π, i, -, -, hπi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let ePi := Coinvariants.piEquiv Λ G (Fin r)
  let i_bar : Coinvariants Λ G P →ₗ[Λ] Fin r → Λ :=
    ePi.toLinearMap ∘ₗ Coinvariants.map i
  let π_bar : (Fin r → Λ) →ₗ[Λ] Coinvariants Λ G P :=
    Coinvariants.map π ∘ₗ ePi.symm.toLinearMap
  have hπi_bar : π_bar ∘ₗ i_bar = .id := by
    have hassoc : π_bar ∘ₗ i_bar =
        Coinvariants.map π ∘ₗ (ePi.symm.toLinearMap ∘ₗ ePi.toLinearMap) ∘ₗ Coinvariants.map i := by
      simp [π_bar, i_bar, LinearMap.comp_assoc]
    rw [hassoc, ePi.symm_comp, LinearMap.id_comp, ← Coinvariants.map_comp, hπi,
      Coinvariants.map_id]
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin r)) i_bar π_bar hπi_bar,
    Module.Basis.hattoriStallingsTrace_apply]
  let y : Fin r → MonoidAlgebra Λ G := fun k ↦ i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k
  have hLHS_k : ∀ k : Fin r,
      ((Pi.basisFun Λ (Fin r)).repr
        ((i_bar ∘ₗ coinvariantEnd Λ ι deg hι hker hPG γ₀.val ∘ₗ π_bar)
          (Pi.basisFun Λ (Fin r) k))) k =
        ∑ g : G, (y k).coeff g := by
    intro k
    let ek : Fin r → Λ := Pi.single k 1
    have hbasis : Pi.basisFun Λ (Fin r) k = ek := Pi.basisFun_apply Λ (Fin r) k
    have hsingle : (fun j : Fin r ↦ single (1 : G) (ek j)) =
        (Pi.single k 1 : Fin r → MonoidAlgebra Λ G) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp [ek, one_def]
      · simp [ek, Pi.single_eq_of_ne hjk]
    have haug : augmentation Λ G (y k) = ∑ g : G, (y k).coeff g := by
      conv_lhs => rw [← sum_coeff_single (y k)]
      rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
      simp
    rw [hbasis]
    simp [i_bar, π_bar, ePi, hsingle, y, haug]
  -- Evaluate each conjugacy-class summand `c` on the same `Λ[G]`-retract.
  have horbit : ∀ c : ConjClasses ι deg d,
      conjClassGroupTrace Λ ι deg hker hPG d c =
        (TauCeti.commutatorSubmodule ℤ Λ).mkQ
          (∑ k : Fin r, ∑ x : { x : F // Quotient.mk R_orb x = c },
            (y k).coeff (degreeFiberEquivGroup hι hker γ₀ x.1)) := by
    intro c
    have hc : c = Quotient.mk R_orb c.out := (Quotient.out_eq c).symm
    conv_lhs => rw [hc, conjClassGroupTrace_mk]
    let γ := c.out
    let Z := centralizerSubgroup ι γ.val.1
    have : Finite (G ⧸ Z.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    let _ : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
    let φZ := mapDomainRingHom Λ Z.subtype
    let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
    let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
    obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
      Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
        fun _ _ ↦ rfl
    let ιZ : Z →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z.subtype
    have hactZ : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = mapDomain ιZ r • p := fun r p ↦ by
      have hcomp : r • p = φZ r • p := rfl
      rw [hcomp, hPG]
      simp [φZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
    let uZ := ιZ.singleSMulLinearMap
      (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ.val) P hactZ
    rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ.val (fun _ _ ↦ rfl) uZ
      (by simp [uZ])]
    let i_Z : P →ₗ[MonoidAlgebra Λ Z] Fin r → MonoidAlgebra Λ G :=
      { toFun := i, map_add' := map_add i,
        map_smul' := fun s p ↦ by rw [RingHom.id_apply]; exact map_smul i (φZ s) p }
    let π_Z : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ Z] P :=
      { toFun := π, map_add' := map_add π,
        map_smul' := fun s v ↦ by rw [RingHom.id_apply]; exact map_smul π (φZ s) v }
    have hπi_Z : π_Z ∘ₗ i_Z = .id := LinearMap.ext fun p ↦ LinearMap.congr_fun hπi p
    let bCoset := TauCeti.MonoidAlgebra.basisCosets Λ Z.subtype Z.subtype_injective
    let bZ : Module.Basis ((_ : Fin r) × (G ⧸ Z.subtype.range)) (MonoidAlgebra Λ Z)
        (Fin r → MonoidAlgebra Λ G) := Pi.basis fun _ ↦ bCoset
    rw [LinearMap.hattoriStallingsGroupTrace_apply,
      LinearMap.hattoriStallingsTrace_eq_of_retract bZ i_Z π_Z hπi_Z,
      Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ]
    congr 1
    simp only [coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← (orbitCosetEquiv hker c).sum_comp]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    let gγ := degreeFiberEquivGroup hι hker γ₀ γ
    have hγ_eq : γ.val = toNonnegSubmonoid ι deg hker gγ⁻¹ * γ₀.val := by
      ext
      simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv]
      exact eq_inv_mul_of_mul_eq (ι_degreeFiberEquivGroup_mul hι hker γ₀ γ)
    have hb : bZ ⟨k, q⟩ =
        (single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • Pi.single k (1 : MonoidAlgebra Λ G) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp [bZ, bCoset]
      · simp [bZ, Pi.single_eq_of_ne hjk]
    have himg : ((i_Z ∘ₗ uZ ∘ₗ π_Z) (bZ ⟨k, q⟩)) k =
        single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) * y k := by
      rw [hb]
      have hπ : π_Z ((single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • Pi.single k 1) =
          (single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • π (Pi.single k 1) :=
        map_smul π (single q.out⁻¹ (1 : Λ)) (Pi.single k 1)
      have hu : uZ ((single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • π (Pi.single k 1)) =
          (single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) : MonoidAlgebra Λ G) •
            (single γ₀.val (1 : Λ) • π (Pi.single k 1)) := by
        rw [MonoidHom.singleSMulLinearMap_apply, ← elemLinearMap_apply Λ,
          elemLinearMap_single_smul hι hPG γ.val q.out⁻¹, elemLinearMap_apply]
        nth_rw 2 [hγ_eq]
        rw [hPG (single _ 1), hPG (single _ 1)]
        simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single,
          one_mul, map_mul, mul_assoc]
      have hi : i_Z ((single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) :
            MonoidAlgebra Λ G) • (single γ₀.val (1 : Λ) • π (Pi.single k 1))) k =
          single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) * y k :=
        congrFun (map_smul i _ _) k
      simpa [LinearMap.comp_apply, hπ, hu] using hi
    have hidx : (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹)⁻¹ * q.out⁻¹ =
        degreeFiberEquivGroup hι hker γ₀ ((orbitCosetEquiv hker c q).1) := by
      have hO : (orbitCosetEquiv hker c q).1 = DegreeFiber.conj hker q.out γ := rfl
      rw [hO]
      apply hι
      apply mul_right_cancel (b := (DegreeFiber.conj hker q.out γ).val.1)
      rw [ι_degreeFiberEquivGroup_mul hι hker γ₀ (DegreeFiber.conj hker q.out γ)]
      simp only [DegreeFiber.val_conj, coe_conjNonneg, mul_inv_rev, inv_inv, map_mul, map_inv,
        ι_conjAut_apply]
      have hgrp : ι gγ * (γ.val.1 * ι q.out * γ.val.1⁻¹) * (ι q.out)⁻¹ *
          (ι q.out * γ.val.1 * (ι q.out)⁻¹) = ι gγ * γ.val.1 := by group
      rw [hgrp, ι_degreeFiberEquivGroup_mul hι hker γ₀ γ]
    have hrepr := MonoidAlgebra.coeff_one_basisCosets_repr Z
      (((i_Z ∘ₗ uZ ∘ₗ π_Z) (bZ ⟨k, q⟩)) k) q
    have hbasis_repr : (bZ.repr ((i_Z ∘ₗ uZ ∘ₗ π_Z) (bZ ⟨k, q⟩)) ⟨k, q⟩).coeff 1 =
        (bCoset.repr (((i_Z ∘ₗ uZ ∘ₗ π_Z) (bZ ⟨k, q⟩)) k) q).coeff 1 := by
      simp [bZ]
    rw [hbasis_repr, hrepr, himg, coeff_single_mul_apply, one_mul, hidx]
  simp only [hLHS_k, horbit, ← map_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpart : ∑ c : ConjClasses ι deg d, ∑ x : { x : F // Quotient.mk R_orb x = c },
      (y k).coeff (degreeFiberEquivGroup hι hker γ₀ x.1) =
      ∑ x : F, (y k).coeff (degreeFiberEquivGroup hι hker γ₀ x) :=
    (Fintype.sum_sigma (f := fun p :
        (c : ConjClasses ι deg d) × { x : F // Quotient.mk R_orb x = c } ↦
      (y k).coeff (degreeFiberEquivGroup hι hker γ₀ p.2.1))).symm.trans
      ((Equiv.sigmaFiberEquiv (Quotient.mk R_orb)).sum_comp
        (fun x ↦ (y k).coeff (degreeFiberEquivGroup hι hker γ₀ x)))
  rw [hpart]
  exact ((degreeFiberEquivGroup hι hker γ₀).sum_comp (fun g ↦ (y k).coeff g)).symm

end Coinvariants

/-! ### Commutative coefficient rings and `ℤ/ℓⁿ` coefficient descent (Lemma 64.15.9) -/

section CommRing

variable (A : Type*) [CommRing A] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)

/-- Scalar-valued centralizer group-ring trace `Tr_A^{Z_γ}(γ, P) ∈ A` over a commutative ring
`A`. -/
def centralizerProjectiveGroupTrace {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) : A :=
  TauCeti.cyclicQuotientEquivOfCommRing ℤ A (centralizerGroupTrace A ι deg hker hPG γ)

variable {A ι deg hker}

theorem centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace A ι deg hker hPG γ =
      (TauCeti.commutatorSubmodule ℤ A).mkQ
        (centralizerProjectiveGroupTrace A ι deg hker hPG γ) := by
  rw [centralizerProjectiveGroupTrace, ← TauCeti.cyclicQuotientEquivOfCommRing_symm_apply]
  exact ((TauCeti.cyclicQuotientEquivOfCommRing ℤ A).symm_apply_apply _).symm

/-- Scalar-valued form of Lemma 64.15.4 over a commutative ring `A`:
`Tr_A(γ, P) = |Z_γ| * Tr_A^{Z_γ}(γ, P)`. -/
theorem projectiveTrace_elemLinearMap_eq_card_centralizer_mul
    (hι : Function.Injective ι) {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [IsScalarTower A (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    [Module.Finite A P] [Module.Projective A P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    LinearMap.projectiveTrace A P (elemLinearMap A P γ) =
      (Nat.card (centralizerSubgroup ι γ.1) : A) *
        centralizerProjectiveGroupTrace A ι deg hker hPG γ := by
  have h := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom
    (hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul hι hPG γ)
  simpa [LinearMap.hattoriStallingsTrace_eq_projectiveTrace,
    centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace, map_nsmul, nsmul_eq_mul] using h

/-- **Scalar extension of `centralizerGroupTrace`** along any ring homomorphism `φ : Λ →+* Λ'`. -/
theorem centralizerGroupTrace_balancedExtension {Λ Λ' : Type*} [Ring Λ] [Ring Λ']
    (φ : Λ →+* Λ') {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ' ι deg hker
        (BalancedExtension.monoidAlgebraModule_comp_mapDomain φ (nonnegSubmonoid deg) P
          (toNonnegSubmonoid ι deg hker) hPG) γ =
      TauCeti.cyclicQuotientRingHomMap φ (centralizerGroupTrace Λ ι deg hker hPG γ) := by
  let Z := centralizerSubgroup ι γ.1
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let ιZ : Z →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z.subtype
  have hactZ : ∀ (r : MonoidAlgebra Λ Z) (p : P), r • p = mapDomain ιZ r • p := fun r p ↦ by
    have hcomp : r • p = φZ r • p := rfl
    rw [hcomp, hPG]
    simp [φZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
  let uZ := ιZ.singleSMulLinearMap
    (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ) P hactZ
  let eZ := BalancedExtension.monoidAlgebraEquiv φ Z P
  let uZ' : Module.End (MonoidAlgebra Λ' Z) (BalancedExtension φ P) :=
    eZ.conjRingEquiv (BalancedExtension.map (mapRingHom Z φ) uZ)
  have huZ' : ∀ x : BalancedExtension φ P, uZ' x = single γ (1 : Λ') • x := by
    intro x
    induction x using BalancedExtension.induction_on with
    | tmul s p =>
      have hconj : uZ' (BalancedExtension.tmul φ s p) =
          eZ (BalancedExtension.map (mapRingHom Z φ) uZ
            (eZ.symm (BalancedExtension.tmul φ s p))) := by
        simp [uZ']
      rw [hconj]
      simp only [eZ, BalancedExtension.monoidAlgebraEquiv_symm_tmul, BalancedExtension.map_tmul]
      rw [BalancedExtension.tmul_eq_smul_one_tmul (f := mapRingHom Z φ) (single (1 : Z) s),
        (BalancedExtension.monoidAlgebraEquiv φ Z P).map_smul,
        BalancedExtension.monoidAlgebraEquiv_tmul_one,
        BalancedExtension.monoidAlgebraModule_single_smul_tmul, mul_one,
        BalancedExtension.monoidAlgebraModule_single_smul_tmul, one_mul]
      have hp1 : (single (1 : Z) (1 : Λ) : MonoidAlgebra Λ Z) • uZ p = single γ (1 : Λ) • p := by
        rw [← one_def, one_smul]
        simp [uZ]
      rw [hp1]
    | add a b ha hb => rw [map_add, smul_add, ha, hb]
  have hPZ' := BalancedExtension.monoidAlgebraModule_comp_mapDomain φ G P Z.subtype
    fun _ _ ↦ rfl
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace
    (BalancedExtension.monoidAlgebraModule_comp_mapDomain φ (nonnegSubmonoid deg) P
      (toNonnegSubmonoid ι deg hker) hPG) γ hPZ' uZ' huZ',
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ (by simp [uZ]),
    LinearMap.hattoriStallingsGroupTrace_conj,
    LinearMap.hattoriStallingsGroupTrace_balancedExtension_mapRingHom]

/-- **`ℤ/ℓⁿ` coefficient descent for centralizer group-ring traces** (Stacks Project,
Section 64.15, Lemma 64.15.9). Let `ℓ` be a prime and suppose the `ℓ`-adic valuation of `|Z_γ|`
(for instance that of `|G|`) is at most `v`. If `P` is a `(ℤ/ℓ^{n+v})[Γ]`-module finite projective
over `(ℤ/ℓ^{n+v})[G]` whose `(ℤ/ℓ^{n+v})`-trace at `γ` equals `|Z_γ| * t`, then the `Z_γ`-group
trace of `γ` on `P / ℓⁿ P = (ℤ/ℓⁿ) ⊗_{ℤ/ℓ^{n+v}} P` equals `t mod ℓⁿ`. -/
theorem centralizerProjectiveGroupTrace_zmod_eq_castHom (hι : Function.Injective ι)
    {ℓ n v : ℕ} [Fact ℓ.Prime]
    {P : Type*} [AddCommGroup P] [Module (ZMod (ℓ ^ (n + v))) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) (nonnegSubmonoid deg)) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v)))
      (MonoidAlgebra (ZMod (ℓ ^ (n + v))) (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Finite (ZMod (ℓ ^ (n + v))) P] [Module.Projective (ZMod (ℓ ^ (n + v))) P]
    (hPG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (p : P),
      r • p = mapDomainRingHom (ZMod (ℓ ^ (n + v))) (toNonnegSubmonoid ι deg hker) r • p)
    {γ : nonnegSubmonoid deg}
    (hv : (Nat.card (centralizerSubgroup ι γ.1)).factorization ℓ ≤ v)
    {t : ZMod (ℓ ^ (n + v))}
    (ht : LinearMap.projectiveTrace (ZMod (ℓ ^ (n + v))) P
      (elemLinearMap (ZMod (ℓ ^ (n + v))) P γ) =
      (Nat.card (centralizerSubgroup ι γ.1) : ZMod (ℓ ^ (n + v))) * t) :
    let π := ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n))
    centralizerProjectiveGroupTrace (ZMod (ℓ ^ n)) ι deg hker
        (BalancedExtension.monoidAlgebraModule_comp_mapDomain π (nonnegSubmonoid deg) P
          (toNonnegSubmonoid ι deg hker) hPG) γ =
      π t := by
  intro π
  have hmul : (Nat.card (centralizerSubgroup ι γ.1) : ZMod (ℓ ^ (n + v))) *
      centralizerProjectiveGroupTrace (ZMod (ℓ ^ (n + v))) ι deg hker hPG γ =
      (Nat.card (centralizerSubgroup ι γ.1) : ZMod (ℓ ^ (n + v))) * t := by
    rw [← projectiveTrace_elemLinearMap_eq_card_centralizer_mul hι hPG γ, ht]
  have hcard : Nat.card (centralizerSubgroup ι γ.1) ≠ 0 := Nat.card_pos.ne'
  have hcast := ZMod.castHom_pow_eq_of_natCast_mul_eq (Fact.out : ℓ.Prime) hcard hv hmul
  have hbase := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ (ZMod (ℓ ^ n)))
    (centralizerGroupTrace_balancedExtension π hPG γ)
  rw [centralizerProjectiveGroupTrace, hbase,
    centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace,
    TauCeti.cyclicQuotientRingHomMap_mkQ, TauCeti.cyclicQuotientEquivOfCommRing_mkQ]
  exact hcast

end CommRing

end TauCeti.MonoidExtension

end
