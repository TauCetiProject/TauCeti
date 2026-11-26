/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.PseudoIsomorphism
public import TauCeti.RingTheory.Polynomial.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.PowerSeries.Ideal

import TauCeti.Algebra.Module.Submodule.Pointwise
import TauCeti.GroupTheory.Index.Exact
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The cyclotomic delta submodule

For a module `M` over `O⟦X⟧`, its delta submodule is the increasing union of the kernels of
`ωₙ = (1 + X) ^ (p ^ n) - 1`. Linear maps preserve this submodule, injective maps reflect it, and
linear maps with finite kernel and cokernel (in particular pseudo-isomorphisms over a local
noetherian `O` with finite residue field when `O⟦X⟧` has Krull dimension `2`) preserve the
finiteness of scalar multiples `a • M_δ`.
On a vertical block `O⟦X⟧ ⧸ (ϖ ^ m)` over a local domain with prime `ϖ` and `p ≠ 0`, the delta
submodule vanishes.

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
open scoped Pointwise

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

section Transport

/-- A linear map with finite kernel reflects the finiteness of `a • deltaSubmodule p O _`. -/
theorem finite_smul_deltaSubmodule_of_finite_ker {p : ℕ} {O M N : Type*} [CommRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [AddCommGroup N] [Module O⟦X⟧ N] {f : M →ₗ[O⟦X⟧] N}
    (hker : Finite (LinearMap.ker f)) (a : O⟦X⟧)
    (hN : Finite ↥(a • deltaSubmodule p O N)) :
    Finite ↥(a • deltaSubmodule p O M) := by
  have hmap (x : M) (hx : x ∈ a • deltaSubmodule p O M) : f x ∈ a • deltaSubmodule p O N := by
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨f y, f.map_deltaSubmodule_le p ⟨y, hy, rfl⟩, (map_smul f a y).symm⟩
  let g := f.restrict hmap
  have : Finite (LinearMap.ker g) := by
    refine Finite.of_injective (fun x : LinearMap.ker g ↦
      (⟨x.val.val, congrArg Subtype.val x.property⟩ : LinearMap.ker f)) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj hxy))
  exact (LinearMap.exact_subtype_ker_map g).finite

/-- A surjective linear map with finite kernel preserves the finiteness of
`a • deltaSubmodule p O _`. -/
private theorem finite_smul_deltaSubmodule_of_surjective_of_finite_ker {p : ℕ} {O M P : Type*}
    [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M] [AddCommGroup P] [Module O⟦X⟧ P]
    {g : M →ₗ[O⟦X⟧] P} (hg : Function.Surjective g) (hker : Finite (LinearMap.ker g)) (a : O⟦X⟧)
    (hM : Finite ↥(a • deltaSubmodule p O M)) :
    Finite ↥(a • deltaSubmodule p O P) := by
  classical
  by_contra hinf
  have : Infinite ↥(a • deltaSubmodule p O P) := not_finite_iff_infinite.mp hinf
  cases nonempty_fintype ↥(a • deltaSubmodule p O M)
  cases nonempty_fintype (LinearMap.ker g)
  -- Suppose `a • P_δ` is infinite, and pick `B = #(a • M_δ) · #(ker g) + 1` distinct elements
  -- `e i = a • z i` with `z i ∈ P_δ`.
  let B := Fintype.card ↥(a • deltaSubmodule p O M) * Fintype.card (LinearMap.ker g) + 1
  let e : Fin B → ↥(a • deltaSubmodule p O P) :=
    fun i ↦ Infinite.natEmbedding ↥(a • deltaSubmodule p O P) i
  have hz : ∀ i : Fin B, ∃ z ∈ deltaSubmodule p O P, a • z = (e i).val := fun i ↦
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (e i).property
  choose z hz_mem hz_smul using hz
  -- All `B` witnesses `z i` are killed by a common cyclotomic element `ω = (1 + X) ^ p ^ m₀ - 1`.
  choose m hm using fun i ↦ (mem_deltaSubmodule p O P (z i)).mp (hz_mem i)
  let m₀ := Finset.univ.sup m
  let ω : O⟦X⟧ := (1 + X) ^ p ^ m₀ - 1
  have hωz (i : Fin B) : ω • z i = 0 :=
    (mem_torsionBy_iff _ _).mp <|
      monotone_torsionBy_one_add_X_pow_sub_one p O P (Finset.le_sup (Finset.mem_univ i))
        ((mem_torsionBy_iff _ _).mpr (hm i))
  -- Lift each `z i` along `g` to `x i ∈ M`; then `κ i = ω • x i` lies in `ker g`. Subtracting a
  -- single reference lift `x₀ k` per kernel class `k = κ j` kills the `ω`-multiple, so
  -- `x i - x₀ (κ i) ∈ M_δ`.
  choose x hgx using fun i ↦ hg (z i)
  let κ : Fin B → LinearMap.ker g := fun i ↦
    ⟨ω • x i, by rw [LinearMap.mem_ker, map_smul, hgx, hωz]⟩
  let x₀ : LinearMap.ker g → M := fun k ↦ if h : ∃ j, κ j = k then x h.choose else 0
  have hdiff_mem (i : Fin B) : x i - x₀ (κ i) ∈ deltaSubmodule p O M := by
    refine (mem_deltaSubmodule p O M _).mpr ⟨m₀, ?_⟩
    dsimp only [x₀]
    split_ifs with h
    · have hκ : (κ h.choose).val = (κ i).val := congrArg Subtype.val h.choose_spec
      simpa only [smul_sub, sub_eq_zero, ω] using hκ.symm
    · exact absurd ⟨i, rfl⟩ h
  -- Map `Fin B` into `(a • M_δ) × ker g` via `Φ i = (a • (x i - x₀ (κ i)), κ i)`. Equal second
  -- components fix `x₀ (κ i)`, so equal first components give `a • x i₁ = a • x i₂`, hence
  -- `e i₁ = e i₂` after applying `g`, making `Φ` injective and contradicting the choice of `B`.
  let Φ : Fin B → ↥(a • deltaSubmodule p O M) × LinearMap.ker g := fun i ↦
    (⟨a • (x i - x₀ (κ i)), Submodule.smul_mem_pointwise_smul _ _ _ (hdiff_mem i)⟩, κ i)
  have hΦ : Function.Injective Φ := fun i₁ i₂ h ↦ by
    have h₂ : κ i₁ = κ i₂ := congrArg Prod.snd h
    have h₁ : a • (x i₁ - x₀ (κ i₁)) = a • (x i₂ - x₀ (κ i₂)) :=
      congrArg Subtype.val (congrArg Prod.fst h)
    rw [h₂, smul_sub, smul_sub, sub_left_inj] at h₁
    have he : (e i₁).val = (e i₂).val := by
      rw [← hz_smul i₁, ← hz_smul i₂, ← hgx i₁, ← hgx i₂, ← map_smul, ← map_smul, h₁]
    exact Fin.ext ((Infinite.natEmbedding _).injective (Subtype.ext he))
  have hcard := Fintype.card_le_of_injective Φ hΦ
  rw [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

/-- Passage from a submodule `I` of finite index in `N` preserves the finiteness of
`a • deltaSubmodule p O _`. -/
private theorem finite_smul_deltaSubmodule_of_finite_quotient {p : ℕ} {O N : Type*} [CommRing O]
    [AddCommGroup N] [Module O⟦X⟧ N] (I : Submodule O⟦X⟧ N) (hcoker : Finite (N ⧸ I)) (a : O⟦X⟧)
    (hI : Finite ↥(a • deltaSubmodule p O I)) :
    Finite ↥(a • deltaSubmodule p O N) := by
  have hmap : Finite ↥((a • deltaSubmodule p O I).map I.subtype) :=
    Finite.of_equiv _ (Submodule.equivMapOfInjective I.subtype I.subtype_injective _).toEquiv
  rw [Submodule.map_pointwise_smul, Submodule.map_deltaSubmodule_subtype] at hmap
  exact Submodule.finite_pointwise_smul_of_finite_quotient hcoker hmap

/-- A linear map with finite kernel and finite cokernel preserves and reflects the finiteness of
`a • deltaSubmodule p O _`. -/
theorem finite_smul_deltaSubmodule_iff_of_finite_ker_of_finite_coker {p : ℕ} {O M N : Type*}
    [CommRing O] [AddCommGroup M] [Module O⟦X⟧ M] [AddCommGroup N] [Module O⟦X⟧ N]
    {f : M →ₗ[O⟦X⟧] N} (hker : Finite (LinearMap.ker f))
    (hcoker : Finite (N ⧸ LinearMap.range f)) (a : O⟦X⟧) :
    Finite ↥(a • deltaSubmodule p O M) ↔ Finite ↥(a • deltaSubmodule p O N) := by
  refine ⟨fun hM ↦ ?_, finite_smul_deltaSubmodule_of_finite_ker hker a⟩
  have hker' : Finite (LinearMap.ker f.rangeRestrict) := by
    rw [LinearMap.ker_rangeRestrict]
    exact hker
  exact finite_smul_deltaSubmodule_of_finite_quotient (LinearMap.range f) hcoker a
    (finite_smul_deltaSubmodule_of_surjective_of_finite_ker f.surjective_rangeRestrict hker' a hM)

/-- Over a local Noetherian coefficient ring `O` with finite residue field such that `O⟦X⟧` has
Krull dimension `2`, a pseudo-isomorphism preserves the finiteness of `a • deltaSubmodule p O _`. -/
theorem IsPseudoIsomorphism.finite_smul_deltaSubmodule_iff {p : ℕ} {O M N : Type*} [CommRing O]
    [IsLocalRing O] [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]
    (hdim : ringKrullDim O⟦X⟧ = 2) [AddCommGroup M] [Module O⟦X⟧ M] [AddCommGroup N]
    [Module O⟦X⟧ N] {f : M →ₗ[O⟦X⟧] N} (hf : IsPseudoIsomorphism f) (a : O⟦X⟧) :
    Finite ↥(a • deltaSubmodule p O M) ↔ Finite ↥(a • deltaSubmodule p O N) := by
  obtain ⟨hker, hcoker⟩ := (isPseudoIsomorphism_iff_finite hdim).mp hf
  exact finite_smul_deltaSubmodule_iff_of_finite_ker_of_finite_coker hker hcoker a

end Transport

/-- The cyclotomic delta submodule of a vertical block `O⟦X⟧ ⧸ (ϖ ^ m)` vanishes. -/
@[simp]
theorem deltaSubmodule_quotient_span_C_pow_eq_bot {p : ℕ} [NeZero p] {O : Type*} [CommRing O]
    [IsDomain O] [IsLocalRing O] {ϖ : O} (hϖ : Prime ϖ) (m : ℕ) :
    deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) = ⊥ := by
  refine eq_bot_iff.mpr ((deltaSubmodule_le_iff p O _).mpr fun k ↦ ?_)
  exact (torsionBy_quotient_span_C_pow_one_add_X_pow_sub_one_eq_bot hϖ
    (pow_ne_zero k (NeZero.ne p)) m).le

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
