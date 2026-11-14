/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# The cyclotomic-primary submodule

The cyclotomic-primary submodule consists of elements killed by a power of some
`ωₙ = (1 + X) ^ (p ^ n) - 1`. Unlike the delta submodule, it retains higher powers of
cyclotomic factors. It is the saturation obtained by repeatedly taking the preimage of the
delta submodule of the quotient. Its quotient has zero delta submodule.

For a noetherian power-series module, one power of one `ωₙ` kills this submodule. When the
coefficient ring is `I`-adically complete for an ideal `I` containing the prime `p`, that power is
distinguished at `I`, so the submodule is finite over the coefficients.
Thus it separates the cyclotomic-primary part before studying the remaining Iwasawa module.

The construction uses Mathlib's `Ideal.primaryComponent` for the ideals `(ωₙ)`.

## References

J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
§5.3, especially (5.3.17)–(5.3.20).
-/

public noncomputable section

open PowerSeries Submodule

namespace TauCeti.Iwasawa

variable (p : ℕ) (O M : Type*) [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]

/-- The elements killed by a power of a finite-level cyclotomic element. -/
def cyclotomicPrimarySubmodule : Submodule O⟦X⟧ M :=
  ⨆ n : ℕ, (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M

/-- The cyclotomic-primary submodule is the supremum of the finite-level primary components. -/
theorem cyclotomicPrimarySubmodule_def :
    cyclotomicPrimarySubmodule p O M =
      ⨆ n : ℕ, (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M := (rfl)

variable {O M} in
/-- If `a` divides `b`, then every vector killed by `a` is killed by `b`. -/
private theorem smul_eq_zero_of_dvd {a b : O⟦X⟧} (hab : a ∣ b) {x : M} (hx : a • x = 0) :
    b • x = 0 := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_comm, mul_smul, hx, smul_zero]

/-- The primary components defining the cyclotomic-primary submodule increase with the level. -/
theorem monotone_primaryComponent_span_one_add_X_pow_sub_one :
    Monotone fun n : ℕ ↦
      (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M := by
  intro m n hmn x hx
  obtain ⟨k, hk⟩ := (Ideal.mem_primaryComponent_span_singleton_iff _).mp hx
  exact (Ideal.mem_primaryComponent_span_singleton_iff _).mpr
    ⟨k, smul_eq_zero_of_dvd
      (pow_dvd_pow_of_dvd (dvd_pow_sub_one_of_dvd (pow_dvd_pow p hmn)) k) hk⟩

/-- An element is cyclotomic-primary exactly when a power of some `ωₙ` kills it. -/
@[simp]
theorem mem_cyclotomicPrimarySubmodule (x : M) :
    x ∈ cyclotomicPrimarySubmodule p O M ↔
      ∃ n k : ℕ, (((1 + X) ^ p ^ n - 1 : O⟦X⟧) ^ k) • x = 0 := by
  rw [cyclotomicPrimarySubmodule, Submodule.mem_iSup_of_directed _
    (monotone_primaryComponent_span_one_add_X_pow_sub_one p O M).directed_le]
  simp only [Ideal.mem_primaryComponent_span_singleton_iff]

/-- Every delta element is cyclotomic-primary. -/
theorem deltaSubmodule_le_cyclotomicPrimarySubmodule :
    deltaSubmodule p O M ≤ cyclotomicPrimarySubmodule p O M := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_deltaSubmodule p O M x).mp hx
  exact (mem_cyclotomicPrimarySubmodule p O M x).mpr ⟨n, 1, by simpa using hn⟩

/-- Each finite-level primary component belongs to the cyclotomic-primary submodule. -/
theorem primaryComponent_le_cyclotomicPrimarySubmodule (n : ℕ) :
    (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M ≤
      cyclotomicPrimarySubmodule p O M :=
  le_iSup (fun n : ℕ ↦ (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M) n

/-- A submodule contains the cyclotomic-primary part if it contains each `(ωₙ)`-primary part. -/
theorem cyclotomicPrimarySubmodule_le_iff {N : Submodule O⟦X⟧ M} :
    cyclotomicPrimarySubmodule p O M ≤ N ↔
      ∀ n : ℕ, (Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)}).primaryComponent M ≤ N := by
  rw [cyclotomicPrimarySubmodule, iSup_le_iff]

/-- Start at zero and repeatedly take the preimage of the delta submodule of the quotient. -/
def cyclotomicPrimaryFiltration : ℕ → Submodule O⟦X⟧ M
  | 0 => ⊥
  | r + 1 => (deltaSubmodule p O (M ⧸ cyclotomicPrimaryFiltration r)).comap
      (cyclotomicPrimaryFiltration r).mkQ

/-- The cyclotomic-primary filtration starts at zero. -/
@[simp]
theorem cyclotomicPrimaryFiltration_zero : cyclotomicPrimaryFiltration p O M 0 = ⊥ := (rfl)

/-- The next filtration step is the preimage of the delta submodule of the quotient. -/
theorem cyclotomicPrimaryFiltration_succ (r : ℕ) :
    cyclotomicPrimaryFiltration p O M (r + 1) =
      (deltaSubmodule p O (M ⧸ cyclotomicPrimaryFiltration p O M r)).comap
        (cyclotomicPrimaryFiltration p O M r).mkQ := (rfl)

/-- A vector enters the next filtration step when a cyclotomic element carries it into
the preceding step. -/
theorem mem_cyclotomicPrimaryFiltration_succ (r : ℕ) (x : M) :
    x ∈ cyclotomicPrimaryFiltration p O M (r + 1) ↔
      ∃ n : ℕ, ((1 + X) ^ p ^ n - 1 : O⟦X⟧) • x ∈
        cyclotomicPrimaryFiltration p O M r := by
  simp only [cyclotomicPrimaryFiltration_succ, mem_comap, mem_deltaSubmodule,
    Submodule.mkQ_apply]
  simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/-- The `r`-th step consists exactly of vectors killed by `ωₙ ^ r` for some level `n`. -/
theorem mem_cyclotomicPrimaryFiltration (r : ℕ) (x : M) :
    x ∈ cyclotomicPrimaryFiltration p O M r ↔
      ∃ n : ℕ, (((1 + X) ^ p ^ n - 1 : O⟦X⟧) ^ r) • x = 0 := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
    rw [mem_cyclotomicPrimaryFiltration_succ]
    simp only [ih]
    constructor
    · rintro ⟨n, m, hm⟩
      let l := max m n
      have hml : ((1 + X) ^ p ^ m - 1 : O⟦X⟧) ∣ (1 + X) ^ p ^ l - 1 :=
        dvd_pow_sub_one_of_dvd (pow_dvd_pow p (le_max_left m n))
      have hnl : ((1 + X) ^ p ^ n - 1 : O⟦X⟧) ∣ (1 + X) ^ p ^ l - 1 :=
        dvd_pow_sub_one_of_dvd (pow_dvd_pow p (le_max_right m n))
      refine ⟨l, smul_eq_zero_of_dvd
        (by simpa [pow_succ] using mul_dvd_mul (pow_dvd_pow_of_dvd hml r) hnl)
        (by simpa only [mul_smul] using hm)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, n, by simpa only [pow_succ, mul_smul] using hn⟩

/-- The recursive cyclotomic-primary filtration is increasing. -/
theorem monotone_cyclotomicPrimaryFiltration : Monotone (cyclotomicPrimaryFiltration p O M) := by
  intro r s hrs x hx
  obtain ⟨n, hn⟩ := (mem_cyclotomicPrimaryFiltration p O M r x).mp hx
  exact (mem_cyclotomicPrimaryFiltration p O M s x).mpr
    ⟨n, smul_eq_zero_of_dvd (pow_dvd_pow _ hrs) hn⟩

/-- The first filtration step is the delta submodule. -/
@[simp]
theorem cyclotomicPrimaryFiltration_one :
    cyclotomicPrimaryFiltration p O M 1 = deltaSubmodule p O M := by
  ext x
  simp [mem_cyclotomicPrimaryFiltration]

/-- The cyclotomic-primary submodule is the union of the recursive preimages of delta. -/
theorem cyclotomicPrimarySubmodule_eq_iSup_filtration :
    cyclotomicPrimarySubmodule p O M = ⨆ r : ℕ, cyclotomicPrimaryFiltration p O M r := by
  ext x
  rw [Submodule.mem_iSup_of_directed _
    (monotone_cyclotomicPrimaryFiltration p O M).directed_le]
  simp only [mem_cyclotomicPrimarySubmodule, mem_cyclotomicPrimaryFiltration]
  exact exists_comm

/-- Membership in the cyclotomic-primary submodule means entering a recursive filtration step. -/
theorem mem_cyclotomicPrimarySubmodule_iff_exists_mem_filtration (x : M) :
    x ∈ cyclotomicPrimarySubmodule p O M ↔
      ∃ r : ℕ, x ∈ cyclotomicPrimaryFiltration p O M r := by
  rw [cyclotomicPrimarySubmodule_eq_iSup_filtration, Submodule.mem_iSup_of_directed _
    (monotone_cyclotomicPrimaryFiltration p O M).directed_le]

/-- On a noetherian module the recursive saturation reaches the cyclotomic-primary part
after finitely many steps. -/
theorem exists_cyclotomicPrimarySubmodule_eq_filtration [IsNoetherian O⟦X⟧ M] :
    ∃ r : ℕ, cyclotomicPrimarySubmodule p O M = cyclotomicPrimaryFiltration p O M r := by
  exact (IsNoetherian.noetherian (cyclotomicPrimarySubmodule p O M)).stabilizes_of_iSup_eq
    ⟨_, monotone_cyclotomicPrimaryFiltration p O M⟩
    (cyclotomicPrimarySubmodule_eq_iSup_filtration p O M).symm

/-- Removing the cyclotomic-primary part leaves no delta elements, even without finiteness
assumptions on the module. -/
@[simp]
theorem deltaSubmodule_quotient_cyclotomicPrimarySubmodule :
    deltaSubmodule p O (M ⧸ cyclotomicPrimarySubmodule p O M) = ⊥ := by
  refine eq_bot_iff.mpr fun q hq ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn⟩ := (mem_deltaSubmodule p O _ _).mp hq
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    mem_cyclotomicPrimarySubmodule_iff_exists_mem_filtration] at hn
  obtain ⟨r, hr⟩ := hn
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
    mem_cyclotomicPrimarySubmodule_iff_exists_mem_filtration]
  exact ⟨r + 1, (mem_cyclotomicPrimaryFiltration_succ p O M r x).mpr ⟨n, hr⟩⟩

/-- On a noetherian module one power of one cyclotomic element kills the entire
cyclotomic-primary submodule. -/
theorem exists_cyclotomicPrimarySubmodule_eq_torsionBy [IsNoetherian O⟦X⟧ M] :
    ∃ n k : ℕ, cyclotomicPrimarySubmodule p O M =
      torsionBy O⟦X⟧ M (((1 + X) ^ p ^ n - 1 : O⟦X⟧) ^ k) := by
  obtain ⟨n, hn⟩ :=
    (IsNoetherian.noetherian (cyclotomicPrimarySubmodule p O M)).stabilizes_of_iSup_eq
      ⟨_, monotone_primaryComponent_span_one_add_X_pow_sub_one p O M⟩ rfl
  obtain ⟨k, hk⟩ := Ideal.exists_le_torsionBySet_pow_of_le_primaryComponent
      (𝔞 := Ideal.span {((1 + X) ^ p ^ n - 1 : O⟦X⟧)})
      (IsNoetherian.noetherian (cyclotomicPrimarySubmodule p O M)) hn.le
  refine ⟨n, k, le_antisymm ?_ ?_⟩
  · simpa only [Ideal.span_singleton_pow, torsionBySet_ideal_span_singleton_eq] using hk
  · intro x hx
    exact (mem_cyclotomicPrimarySubmodule p O M x).mpr ⟨n, k, (mem_torsionBy_iff _ _).mp hx⟩

/-- If the coefficients are `I`-adically complete for an ideal `I` containing the prime `p`, the
cyclotomic-primary part of a noetherian power-series module is finite over the coefficients. -/
theorem finite_cyclotomicPrimarySubmodule [Fact p.Prime]
    [Module O M] [IsScalarTower O O⟦X⟧ M] [IsNoetherian O⟦X⟧ M]
    {I : Ideal O} [IsAdicComplete I O] (hp : (p : O) ∈ I) :
    Module.Finite O (cyclotomicPrimarySubmodule p O M) := by
  obtain ⟨n, k, hnk⟩ := exists_cyclotomicPrimarySubmodule_eq_torsionBy p O M
  have hkill : Module.IsTorsionBy O⟦X⟧ (cyclotomicPrimarySubmodule p O M)
      (((1 + X) ^ p ^ n - 1 : O⟦X⟧) ^ k) := by
    intro x
    apply Subtype.ext
    exact (mem_torsionBy_iff _ _).mp (hnk ▸ x.property)
  have hF := ((TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one
    (Fact.out : p.Prime) hp n).pow k).isWeierstrassFactorizationAt
  apply hF.finite_of_isTorsionBy
  simpa using hkill

/-- A module has no cyclotomic-primary part exactly when it has no delta elements. -/
theorem cyclotomicPrimarySubmodule_eq_bot_iff :
    cyclotomicPrimarySubmodule p O M = ⊥ ↔ deltaSubmodule p O M = ⊥ := by
  refine ⟨fun h ↦ eq_bot_iff.mpr (h ▸ deltaSubmodule_le_cyclotomicPrimarySubmodule p O M),
    fun h ↦ ?_⟩
  apply eq_bot_iff.mpr
  apply (cyclotomicPrimarySubmodule_le_iff p O M).mpr
  intro n
  apply le_of_eq
  apply (Ideal.primaryComponent_span_singleton_eq_bot_iff _).mpr
  apply (isSMulRegular_iff_torsionBy_eq_bot M _).mpr
  exact le_antisymm ((torsionBy_le_deltaSubmodule p O M n).trans h.le) bot_le

/-- Over a domain, for `p ≠ 0`, a torsion-free power-series module has no cyclotomic-primary
part. -/
@[simp]
theorem cyclotomicPrimarySubmodule_eq_bot [NeZero p] [IsDomain O]
    [Module.IsTorsionFree O⟦X⟧ M] : cyclotomicPrimarySubmodule p O M = ⊥ :=
  (cyclotomicPrimarySubmodule_eq_bot_iff p O M).mpr (deltaSubmodule_eq_bot p O M)

/-- Removing the cyclotomic-primary part leaves no cyclotomic-primary elements. -/
@[simp]
theorem cyclotomicPrimarySubmodule_quotient_cyclotomicPrimarySubmodule :
    cyclotomicPrimarySubmodule p O (M ⧸ cyclotomicPrimarySubmodule p O M) = ⊥ :=
  (cyclotomicPrimarySubmodule_eq_bot_iff p O _).mpr
    (deltaSubmodule_quotient_cyclotomicPrimarySubmodule p O M)

/-- The cyclotomic-primary submodule is cyclotomic-primary as a module. -/
@[simp]
theorem cyclotomicPrimarySubmodule_cyclotomicPrimarySubmodule :
    cyclotomicPrimarySubmodule p O (cyclotomicPrimarySubmodule p O M) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨n, k, h⟩ := (mem_cyclotomicPrimarySubmodule p O M x).mp x.property
  refine (mem_cyclotomicPrimarySubmodule p O _ x).mpr ⟨n, k, ?_⟩
  rw [← Submodule.coe_eq_zero, Submodule.coe_smul, h]

end TauCeti.Iwasawa

namespace LinearMap

open TauCeti.Iwasawa

variable {O M N : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]
  [AddCommGroup N] [Module O⟦X⟧ N]

/-- Linear maps preserve the cyclotomic-primary part. -/
theorem map_cyclotomicPrimarySubmodule_le (f : M →ₗ[O⟦X⟧] N) (p : ℕ) :
    (cyclotomicPrimarySubmodule p O M).map f ≤ cyclotomicPrimarySubmodule p O N := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, k, hnk⟩ := (mem_cyclotomicPrimarySubmodule p O M x).mp hx
  exact (mem_cyclotomicPrimarySubmodule p O N (f x)).mpr
    ⟨n, k, by rw [← map_smul, hnk, map_zero]⟩

/-- Injective linear maps reflect the cyclotomic-primary part. -/
@[simp]
theorem comap_cyclotomicPrimarySubmodule_of_injective (f : M →ₗ[O⟦X⟧] N)
    (hf : Function.Injective f) (p : ℕ) :
    (cyclotomicPrimarySubmodule p O N).comap f = cyclotomicPrimarySubmodule p O M := by
  ext x
  simp only [mem_comap, mem_cyclotomicPrimarySubmodule, ← map_smul, ← map_zero f, hf.eq_iff]

end LinearMap

namespace LinearEquiv

open TauCeti.Iwasawa

variable {O M N : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]
  [AddCommGroup N] [Module O⟦X⟧ N]

/-- Linear equivalences identify the cyclotomic-primary parts. -/
@[simp]
theorem map_cyclotomicPrimarySubmodule (e : M ≃ₗ[O⟦X⟧] N) (p : ℕ) :
    (cyclotomicPrimarySubmodule p O M).map e.toLinearMap = cyclotomicPrimarySubmodule p O N := by
  rw [← e.toLinearMap.comap_cyclotomicPrimarySubmodule_of_injective e.injective p,
    Submodule.map_comap_eq_of_surjective e.surjective]

end LinearEquiv

namespace Submodule

open TauCeti.Iwasawa

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]

/-- The cyclotomic-primary part of a submodule is the restriction of the ambient one. -/
@[simp]
theorem comap_cyclotomicPrimarySubmodule_subtype (S : Submodule O⟦X⟧ M) (p : ℕ) :
    (cyclotomicPrimarySubmodule p O M).comap S.subtype = cyclotomicPrimarySubmodule p O S :=
  S.subtype.comap_cyclotomicPrimarySubmodule_of_injective S.subtype_injective p

/-- Taking the cyclotomic-primary submodule commutes with passage to a submodule. -/
@[simp]
theorem map_cyclotomicPrimarySubmodule_subtype (S : Submodule O⟦X⟧ M) (p : ℕ) :
    (cyclotomicPrimarySubmodule p O S).map S.subtype = S ⊓ cyclotomicPrimarySubmodule p O M := by
  rw [← comap_cyclotomicPrimarySubmodule_subtype, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_comm]

end Submodule

namespace TauCeti.Iwasawa

variable (p : ℕ) (O : Type*) [CommRing O]

-- The zero module has zero cyclotomic-primary part, including over the zero ring.
example : cyclotomicPrimarySubmodule p O (Fin 0 → O⟦X⟧) = ⊥ := Subsingleton.elim _ _

-- A free rank-one module has no cyclotomic-primary part.
example [NeZero p] [IsDomain O] : cyclotomicPrimarySubmodule p O O⟦X⟧ = ⊥ := by simp

-- Higher powers are retained: the entire quotient by X² is cyclotomic-primary.
example : cyclotomicPrimarySubmodule p O (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧) ^ 2}) = ⊤ := by
  apply top_unique
  intro x _
  refine (mem_cyclotomicPrimarySubmodule p O _ x).mpr ⟨0, 2, ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [pow_zero, pow_one, add_sub_cancel_left]
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

-- In characteristic zero the same quotient is not all delta: the class of 1 is not delta.
example [CharZero O] [NeZero p] :
    (1 : O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧) ^ 2}) ∉
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧) ^ 2}) := by
  intro h
  obtain ⟨n, hn⟩ := (mem_deltaSubmodule p O _ _).mp h
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {(X : O⟦X⟧) ^ 2})),
    ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    Submodule.Quotient.mk_eq_zero] at hn
  have hc : coeff 1 ((1 + X) ^ p ^ n - 1 : O⟦X⟧) = (p : O) ^ n := by
    have hc := Polynomial.coeff_coe
      (((1 + Polynomial.X) ^ p ^ n - 1) : Polynomial O) 1
    simpa [Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one] using hc
  have hz := PowerSeries.X_pow_dvd_iff.mp
    (Ideal.mem_span_singleton.mp hn) 1 (by decide)
  rw [hc] at hz
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero n (NeZero.ne p)) : ((p ^ n : ℕ) : O) ≠ 0)
    (by simpa only [Nat.cast_pow] using hz)

end TauCeti.Iwasawa
