/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly
public import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# The cyclotomic delta submodule

For a module `M` over `O⟦X⟧`, its delta submodule is the increasing union of the kernels of
`ωₙ = (1 + X) ^ (p ^ n) - 1`. Linear maps preserve this submodule, and injective maps reflect it.

On a noetherian module the union stabilizes at a single kernel. If `O` is noetherian and
`I`-adically complete for an ideal `I` containing the prime `p`, this makes the delta submodule of
a finite `O⟦X⟧`-module finite over `O`: it is a finite module over the quotient by a distinguished
polynomial `ωₙ`. This is the finiteness input for separating cyclotomic factors in growth formulas.
No torsion, characteristic-zero, discrete-valuation or finite-residue-field hypothesis is needed
for this step. The delta submodule is not the whole cyclotomic-primary part: higher powers of a
cyclotomic factor need not be killed by any `ωₙ`.

## References

J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
§5.3, especially Proposition 5.3.17.
-/

public noncomputable section

open PowerSeries Submodule

namespace TauCeti.Iwasawa

variable (p : ℕ) (O M : Type*) [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]

/-- The elements killed by some cyclotomic element `(1 + X) ^ (p ^ n) - 1`. -/
def deltaSubmodule : Submodule O⟦X⟧ M :=
  ⨆ n : ℕ, torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1)

/-- The delta submodule is the supremum of the finite-level cyclotomic kernels. -/
theorem deltaSubmodule_def :
    deltaSubmodule p O M = ⨆ n : ℕ, torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) := (rfl)

/-- A submodule contains the delta submodule exactly when it contains every finite-level kernel. -/
@[simp]
theorem deltaSubmodule_le_iff {N : Submodule O⟦X⟧ M} :
    deltaSubmodule p O M ≤ N ↔ ∀ n : ℕ, torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) ≤ N := by
  rw [deltaSubmodule_def, iSup_le_iff]

/-- The kernels defining the delta submodule increase with the level. -/
theorem monotone_torsionBy_one_add_X_pow_sub_one :
    Monotone fun n : ℕ ↦ torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) := by
  intro m n hmn
  exact torsionBy_le_torsionBy_of_dvd _ _
    (dvd_pow_sub_one_of_dvd (pow_dvd_pow p hmn))

/-- Membership in the delta submodule means being killed at a single finite level. -/
@[simp]
theorem mem_deltaSubmodule (x : M) :
    x ∈ deltaSubmodule p O M ↔ ∃ n : ℕ, ((1 + X) ^ p ^ n - 1 : O⟦X⟧) • x = 0 := by
  rw [deltaSubmodule, Submodule.mem_iSup_of_directed _
    (monotone_torsionBy_one_add_X_pow_sub_one p O M).directed_le]
  simp only [mem_torsionBy_iff]

/-- Each finite-level kernel belongs to the delta submodule. -/
theorem torsionBy_le_deltaSubmodule (n : ℕ) :
    torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) ≤ deltaSubmodule p O M :=
  le_iSup (fun n : ℕ ↦ torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1)) n

/-- On a noetherian module the delta submodule is already one finite-level kernel. -/
theorem exists_deltaSubmodule_eq_torsionBy [IsNoetherian O⟦X⟧ M] :
    ∃ n : ℕ, deltaSubmodule p O M = torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) := by
  exact (IsNoetherian.noetherian (deltaSubmodule p O M)).stabilizes_of_iSup_eq
    ⟨_, monotone_torsionBy_one_add_X_pow_sub_one p O M⟩ rfl

/-- At all sufficiently deep levels, the cyclotomic kernel equals the delta submodule. -/
theorem eventually_deltaSubmodule_eq_torsionBy [IsNoetherian O⟦X⟧ M] :
    ∀ᶠ n : ℕ in Filter.atTop,
      deltaSubmodule p O M = torsionBy O⟦X⟧ M ((1 + X) ^ p ^ n - 1) := by
  obtain ⟨n, hn⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ le_antisymm ?_ ?_⟩
  · rw [hn]
    exact monotone_torsionBy_one_add_X_pow_sub_one p O M hm
  · exact torsionBy_le_deltaSubmodule p O M m

/-- A torsion-free power-series module has zero delta submodule. -/
@[simp]
theorem deltaSubmodule_eq_bot [NeZero p] [IsDomain O] [Module.IsTorsionFree O⟦X⟧ M] :
    deltaSubmodule p O M = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨n, hn⟩ := (mem_deltaSubmodule p O M x).mp hx
  have hne : ((1 + X) ^ p ^ n - 1 : O⟦X⟧) ≠ 0 := by
    have h := (TauCeti.Polynomial.monic_one_add_X_pow_sub_one
      (R := O) (pow_ne_zero n (NeZero.ne p))).ne_zero
    simpa using (Polynomial.coe_injective O).ne h
  exact (smul_eq_zero_iff_right hne).mp hn

/-- Over a complete noetherian coefficient ring, the delta submodule of a finite power-series
module is finite over the coefficients, whenever `p` is prime and lies in the completeness ideal. -/
theorem finite_deltaSubmodule [Fact p.Prime] [IsNoetherianRing O]
    [Module O M] [IsScalarTower O O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    {I : Ideal O} [IsAdicComplete I O] (hp : (p : O) ∈ I) :
    Module.Finite O (deltaSubmodule p O M) := by
  obtain ⟨n, hn⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  have hkill : Module.IsTorsionBy O⟦X⟧ (deltaSubmodule p O M)
      ((1 + X) ^ p ^ n - 1) := by
    intro x
    apply Subtype.ext
    exact (mem_torsionBy_iff _ _).mp (hn ▸ x.property)
  have hF := (TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one
    (Fact.out : p.Prime) hp n).isWeierstrassFactorizationAt
  apply hF.finite_of_isTorsionBy
  simpa using hkill

end TauCeti.Iwasawa

namespace LinearMap

variable {O M N : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]
  [AddCommGroup N] [Module O⟦X⟧ N]

open TauCeti.Iwasawa

/-- Linear maps carry delta elements to delta elements. -/
theorem map_deltaSubmodule_le (f : M →ₗ[O⟦X⟧] N) (p : ℕ) :
    (deltaSubmodule p O M).map f ≤ deltaSubmodule p O N := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := (mem_deltaSubmodule p O M x).mp hx
  exact (mem_deltaSubmodule p O N (f x)).mpr ⟨n, by rw [← map_smul, hn, map_zero]⟩

/-- An injective linear map reflects the delta submodule as well as preserving it. -/
@[simp]
theorem comap_deltaSubmodule_of_injective (f : M →ₗ[O⟦X⟧] N) (hf : Function.Injective f)
    (p : ℕ) : (deltaSubmodule p O N).comap f = deltaSubmodule p O M := by
  ext x
  simp only [Submodule.mem_comap, mem_deltaSubmodule]
  exact exists_congr fun n ↦ by rw [← map_smul, ← map_zero f, hf.eq_iff]

end LinearMap

namespace LinearEquiv

variable {O M N : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]
  [AddCommGroup N] [Module O⟦X⟧ N]

open TauCeti.Iwasawa

/-- Linear equivalences identify the delta submodules. -/
@[simp]
theorem map_deltaSubmodule (e : M ≃ₗ[O⟦X⟧] N) (p : ℕ) :
    (deltaSubmodule p O M).map e.toLinearMap = deltaSubmodule p O N := by
  rw [← e.toLinearMap.comap_deltaSubmodule_of_injective e.injective p,
    Submodule.map_comap_eq_of_surjective e.surjective]

end LinearEquiv

namespace Submodule

open TauCeti.Iwasawa

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M]

/-- Taking the delta submodule commutes with passage to a submodule. -/
@[simp]
theorem map_deltaSubmodule_subtype (S : Submodule O⟦X⟧ M) (p : ℕ) :
    (deltaSubmodule p O S).map S.subtype = S ⊓ deltaSubmodule p O M := by
  rw [← S.subtype.comap_deltaSubmodule_of_injective S.subtype_injective p,
    Submodule.map_comap_eq, Submodule.range_subtype, inf_comm]

end Submodule

namespace TauCeti.Iwasawa

variable (p : ℕ) (O : Type*) [CommRing O]

-- The zero module has no delta elements other than zero.
example : deltaSubmodule p O (Fin 0 → O⟦X⟧) = ⊥ := Subsingleton.elim _ _

-- In particular the free rank-one module has zero delta submodule.
example [NeZero p] [IsDomain O] : deltaSubmodule p O O⟦X⟧ = ⊥ := by simp

-- If X kills the module, every element is already a level-zero delta element.
example : deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) = ⊤ := by
  apply top_unique
  intro x _
  refine (mem_deltaSubmodule p O _ x).mpr ⟨0, ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [pow_zero, pow_one, add_sub_cancel_left]
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

end TauCeti.Iwasawa
