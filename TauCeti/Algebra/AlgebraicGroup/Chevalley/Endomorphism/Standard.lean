/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.FieldEndomorphism
import TauCeti.Algebra.Group.End

/-!
# Standard and based endomorphisms of a Chevalley datum

An endomorphism `F` of `D.points A` is **standard** (`D.IsStandard F`) if it acts on
`D.torusPoints A` via an injective character-lattice endomorphism and maps each root subgroup onto
a root subgroup, and **based** (`D.IsBased F`) if it is standard and maps positive root
subgroups onto positive ones; for standard `F` this is equivalent to
`(D.borelSubgroup A).map F ≤ D.borelSubgroup A`
(`isBased_iff_isStandard_and_map_borelSubgroup_le`). Over a perfect ring, `D.frobenius p k A` is
based (`isBased_frobenius`). Over an infinite field `K`, `hF : D.IsStandard F` has a unique
character map `hF.characterMap`, root permutation `hF.rootPerm` with positive proportionality
(`IsStandard.exists_pos_nsmul_characterMap_coordinateRoot`) and root-permutation rigidity
(`IsStandard.rootPerm_eq_of_isCharacterMap`), and additive root-parameter maps `hF.rootParamHom`
(`IsStandard.rootSubgroupPoints_rootParamHom`), while a based `F` maps `D.positivePoints K` onto
itself (`IsBased.map_positivePoints_eq`); with `[RootableBy Kˣ ℕ]`, `F` maps
`D.rootTorusSubgroup K` (and, when based, `D.borelSubgroup K`) onto itself
(`IsStandard.map_rootTorusSubgroup_eq`, `IsBased.map_borelSubgroup_eq`), and induces `hF.rootUnit`
and `hF.fieldEnd` (bundled as the field automorphism `hF.fieldEquiv`) satisfying
`F (x_α(u)) = x_{hF.rootPerm α}(hF.rootUnit α * hF.fieldEnd α u)`
(`IsStandard.map_rootSubgroupPoints`) and field-endomorphism rigidity
(`IsStandard.fieldEnd_eq_of_isCharacterMap`).

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11; *Lectures on Chevalley Groups*, Ch. 10, Theorems 28–29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum
open Multiplicative
universe v
variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Definitions and general ring properties -/

section CommRing
variable {A : Type v} [CommRing A]

/-- **A standard endomorphism of `D.points A`**: acts on `D.torusPoints A` via an injective
character-lattice endomorphism and maps each root subgroup onto some root subgroup. -/
def IsStandard (F : D.points A →* D.points A) : Prop :=
  (∃ φ : Module.End ℤ (Fin t.rank → ℤ),
    Function.Injective φ ∧ IsCharacterMap (D.torusPoints A) F φ) ∧
    ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
      (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

/-- Unfolding characterization of `D.IsStandard F`. -/
theorem isStandard_def (F : D.points A →* D.points A) :
    D.IsStandard F ↔ (∃ φ : Module.End ℤ (Fin t.rank → ℤ),
      Function.Injective φ ∧ IsCharacterMap (D.torusPoints A) F φ) ∧
      ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
        (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := Iff.rfl

/-- **A based endomorphism of `D.points A`**: a standard endomorphism mapping each positive root
subgroup onto a positive root subgroup. -/
def IsBased (F : D.points A →* D.points A) : Prop :=
  D.IsStandard F ∧ ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
    ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

/-- Unfolding characterization of `D.IsBased F`. -/
theorem isBased_def (F : D.points A →* D.points A) :
    D.IsBased F ↔ D.IsStandard F ∧ ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := Iff.rfl

variable {D} {F F' : D.points A →* D.points A}

/-- Every based endomorphism is standard. -/
theorem IsBased.isStandard (h : D.IsBased F) : D.IsStandard F := ((D.isBased_def F).mp h).1

/-- A standard endomorphism acts on `D.torusPoints A` via some injective character-lattice
endomorphism. -/
theorem IsStandard.exists_isCharacterMap (hF : D.IsStandard F) :
    ∃ φ : Module.End ℤ (Fin t.rank → ℤ),
      Function.Injective φ ∧ IsCharacterMap (D.torusPoints A) F φ :=
  ((D.isStandard_def F).mp hF).1

/-- A standard endomorphism maps each root subgroup onto some root subgroup. -/
theorem IsStandard.exists_map_range_rootSubgroupPoints (hF : D.IsStandard F)
    (α : Fin t.numRoots) : ∃ β : Fin t.numRoots,
      (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range :=
  ((D.isStandard_def F).mp hF).2 α

/-- A based endomorphism maps each positive root subgroup onto some positive root subgroup. -/
theorem IsBased.exists_map_range_rootSubgroupPoints (hF : D.IsBased F) {α : Fin t.numRoots}
    (hα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range :=
  ((D.isBased_def F).mp hF).2 α hα

/-- The identity endomorphism is standard. -/
@[simp] theorem isStandard_id : D.IsStandard (MonoidHom.id (D.points A)) :=
  ⟨⟨1, Function.injective_id, isCharacterMap_id (D.torusPoints A)⟩, fun α => ⟨α, Subgroup.map_id _⟩⟩

/-- The identity endomorphism is based. -/
@[simp] theorem isBased_id : D.IsBased (MonoidHom.id (D.points A)) :=
  ⟨D.isStandard_id, fun α hα => ⟨α, hα, Subgroup.map_id _⟩⟩

/-- Standard endomorphisms are closed under composition. -/
theorem IsStandard.comp (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    D.IsStandard (F.comp F') := by
  obtain ⟨φ, hφ_inj, hφ⟩ := hF.exists_isCharacterMap
  obtain ⟨ψ, hψ_inj, hψ⟩ := hF'.exists_isCharacterMap
  refine ⟨⟨ψ * φ, hψ_inj.comp hφ_inj, hφ.comp hψ⟩, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hF'.exists_map_range_rootSubgroupPoints α
  obtain ⟨γ, hγ⟩ := hF.exists_map_range_rootSubgroupPoints β
  exact ⟨γ, by rw [← Subgroup.map_map, hβ, hγ]⟩

/-- Based endomorphisms are closed under composition. -/
theorem IsBased.comp (hF : D.IsBased F) (hF' : D.IsBased F') : D.IsBased (F.comp F') :=
  ⟨hF.isStandard.comp hF'.isStandard, fun α hα => by
    obtain ⟨β, hβpos, hβ⟩ := hF'.exists_map_range_rootSubgroupPoints hα
    obtain ⟨γ, hγpos, hγ⟩ := hF.exists_map_range_rootSubgroupPoints hβpos
    exact ⟨γ, hγpos, by rw [← Subgroup.map_map, hβ, hγ]⟩⟩

/-- Powers of a standard endomorphism in `Monoid.End` are standard. -/
theorem IsStandard.pow {F : Monoid.End (D.points A)} (hF : D.IsStandard F) (n : ℕ) :
    D.IsStandard (HPow.hPow (α := Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => rw [pow_zero, Monoid.End.one_eq_id]; exact D.isStandard_id
  | succ n ih => rw [pow_succ', Monoid.End.mul_eq_comp]; exact hF.comp ih

/-- Powers of a based endomorphism in `Monoid.End` are based. -/
theorem IsBased.pow {F : Monoid.End (D.points A)} (hF : D.IsBased F) (n : ℕ) :
    D.IsBased (HPow.hPow (α := Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => rw [pow_zero, Monoid.End.one_eq_id]; exact D.isBased_id
  | succ n ih => rw [pow_succ', Monoid.End.mul_eq_comp]; exact hF.comp ih

/-- A standard endomorphism carries the actual torus into itself. -/
theorem IsStandard.map_range_torusPoints_le (hF : D.IsStandard F) :
    (D.torusPoints A).range.map F ≤ (D.torusPoints A).range := by
  obtain ⟨φ, _, hφ⟩ := hF.exists_isCharacterMap; rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨torusPointMap φ s, (hφ.map_apply s).symm⟩

/-- Over a ring with divisible units, a standard endomorphism maps the actual torus onto itself. -/
theorem IsStandard.map_range_torusPoints_eq [RootableBy Aˣ ℕ] (hF : D.IsStandard F) :
    (D.torusPoints A).range.map F = (D.torusPoints A).range :=
  let ⟨_, hφ_inj, hφ⟩ := hF.exists_isCharacterMap; hφ.map_range_eq hφ_inj

/-- A standard endomorphism preserves `D.rootTorusSubgroup A`. -/
theorem IsStandard.map_rootTorusSubgroup_le (hF : D.IsStandard F) :
    (D.rootTorusSubgroup A).map F ≤ D.rootTorusSubgroup A := by
  rw [Subgroup.map_le_iff_le_comap, D.rootTorusSubgroup_le_iff]
  refine ⟨fun α u => ?_, fun s => ?_⟩
  · obtain ⟨β, hβ⟩ := hF.exists_map_range_rootSubgroupPoints α
    obtain ⟨v, hv⟩ := hβ.le ⟨D.rootSubgroupPoints α A u, ⟨u, rfl⟩, rfl⟩
    rw [Subgroup.mem_comap, ← hv]; exact D.rootSubgroupPoints_mem_rootTorusSubgroup β A v
  · obtain ⟨φ, _, hφ⟩ := hF.exists_isCharacterMap
    rw [Subgroup.mem_comap, hφ.map_apply]; exact D.torusPoints_mem_rootTorusSubgroup A _

/-- A based endomorphism preserves `D.positivePoints A`. -/
theorem IsBased.map_positivePoints_le (hF : D.IsBased F) :
    (D.positivePoints A).map F ≤ D.positivePoints A := by
  rw [Subgroup.map_le_iff_le_comap, D.positivePoints_le_iff]; intro α hα u
  obtain ⟨β, hβpos, hβ⟩ := hF.exists_map_range_rootSubgroupPoints hα
  obtain ⟨v, hv⟩ := hβ.le ⟨D.rootSubgroupPoints α A u, ⟨u, rfl⟩, rfl⟩
  rw [Subgroup.mem_comap, ← hv]; exact D.rootSubgroupPoints_mem_positivePoints A hβpos v

/-- A based endomorphism preserves `D.borelSubgroup A`. -/
theorem IsBased.map_borelSubgroup_le (hF : D.IsBased F) :
    (D.borelSubgroup A).map F ≤ D.borelSubgroup A := by
  rw [D.borelSubgroup_def, Subgroup.map_sup]
  exact sup_le_sup hF.map_positivePoints_le hF.isStandard.map_range_torusPoints_le

private noncomputable def IsStandard.rawRootMap (hF : D.IsStandard F) (α : Fin t.numRoots) :=
  (hF.exists_map_range_rootSubgroupPoints α).choose

private theorem IsStandard.map_range_rootSubgroupPoints_rawRootMap (hF : D.IsStandard F) (α) :
    (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints (hF.rawRootMap α) A).range :=
  (hF.exists_map_range_rootSubgroupPoints α).choose_spec

/-- **A standard endomorphism is based iff it preserves `D.borelSubgroup A`.** -/
theorem isBased_iff_isStandard_and_map_borelSubgroup_le (D : ChevalleyDatum t ht)
    {F : D.points A →* D.points A} :
    D.IsBased F ↔ D.IsStandard F ∧ (D.borelSubgroup A).map F ≤ D.borelSubgroup A :=
  ⟨fun h => ⟨h.isStandard, h.map_borelSubgroup_le⟩, fun ⟨hStd, hB⟩ => ⟨hStd, fun α hα => by
    rcases subsingleton_or_nontrivial A with _ | _
    · have hbot (γ) : (D.rootSubgroupPoints γ A).range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr
        fun _ ⟨u, hu⟩ => hu ▸ by rw [Subsingleton.elim u 1, map_one]
      exact ⟨α, hα, by simp [hbot]⟩
    obtain ⟨β, hβ⟩ := hStd.exists_map_range_rootSubgroupPoints α
    refine ⟨β, by_contra fun hβnot => ?_, hβ⟩
    obtain ⟨_, ⟨u, rfl⟩, hx⟩ : D.rootSubgroupPoints β A (ofAdd 1) ∈
        (D.rootSubgroupPoints α A).range.map F := hβ ▸ ⟨ofAdd 1, rfl⟩
    exact D.rootSubgroupPoints_ofAdd_one_ne_one A β
      ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A
        ((not_mem_posRoots_iff_mem_negRoots _ _ _).mp hβnot) (ofAdd 1)).mp
        (hB ⟨_, D.positivePoints_le_borelSubgroup A
          (D.rootSubgroupPoints_mem_positivePoints A hα u), hx⟩))⟩⟩

/-- **Over any perfect ring of exponential characteristic `p`, Frobenius is based.** -/
@[simp] theorem isBased_frobenius (D : ChevalleyDatum t ht) (p k : ℕ) [ExpChar A p]
    [PerfectRing A p] : D.IsBased (D.frobenius p k A) :=
  ⟨⟨⟨(p ^ k : ℕ) • 1, fun _ _ h => nsmul_right_injective (pow_ne_zero k (expChar_ne_zero A p))
      (by simpa only [LinearMap.smul_apply, one_apply_eq_self] using h),
      D.isCharacterMap_frobenius p k A⟩,
      fun α => ⟨α, D.map_range_rootSubgroupPoints_frobenius p k A α⟩⟩,
    fun α hα => ⟨α, hα, D.map_range_rootSubgroupPoints_frobenius p k A α⟩⟩

/-- Over any perfect ring of exponential characteristic `p`, Frobenius is standard. -/
@[simp] theorem isStandard_frobenius (D : ChevalleyDatum t ht) (p k : ℕ) [ExpChar A p]
    [PerfectRing A p] : D.IsStandard (D.frobenius p k A) := (D.isBased_frobenius p k).isStandard

end CommRing

/-! ## Unique character map and root permutation over an infinite field -/

section Field
variable {K : Type v} [Field K] {D} {F F' : D.points K →* D.points K}

private noncomputable def IsStandard.paramHomOf (_ : D.IsStandard F)
    (α β : Fin t.numRoots)
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) : K →+ K :=
  AddMonoidHom.toMultiplicative.symm ((MonoidHom.ofInjective
    (D.rootSubgroupPoints_injective K β)).symm.toMonoidHom.comp
    ((F.comp (D.rootSubgroupPoints α K)).codRestrict _ fun u => by
      rw [← hβ]; exact ⟨_, ⟨u, rfl⟩, rfl⟩))

private theorem IsStandard.rootSubgroupPoints_paramHomOf (hF : D.IsStandard F)
    {α β : Fin t.numRoots}
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) (u : K) :
    D.rootSubgroupPoints β K (ofAdd (hF.paramHomOf α β hβ u)) =
      F (D.rootSubgroupPoints α K (ofAdd u)) := by simp [IsStandard.paramHomOf]

private theorem IsStandard.paramHomOf_surjective (hF : D.IsStandard F) {α β : Fin t.numRoots}
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) :
    Function.Surjective (hF.paramHomOf α β hβ) := fun v => by
  obtain ⟨_, ⟨u, rfl⟩, hFu⟩ : D.rootSubgroupPoints β K (ofAdd v) ∈
      (D.rootSubgroupPoints α K).range.map F := hβ ▸ ⟨ofAdd v, rfl⟩
  have hinj := D.rootSubgroupPoints_injective K β
    ((hF.rootSubgroupPoints_paramHomOf hβ (toAdd u)).trans (by rw [ofAdd_toAdd, hFu]))
  exact ⟨toAdd u, by simpa only [toAdd_ofAdd] using congrArg toAdd hinj⟩

private theorem IsStandard.paramHomOf_ne_zero (hF : D.IsStandard F) {α β : Fin t.numRoots}
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) :
    hF.paramHomOf α β hβ ≠ 0 := fun h0 => by
  obtain ⟨u, hu⟩ := hF.paramHomOf_surjective hβ 1
  exact (one_ne_zero (α := K)) (hu.symm.trans (by simp [h0]))

variable [Infinite K]

/-- Over an infinite field, a standard endomorphism has a unique character map. -/
theorem IsStandard.existsUnique_characterMap (hF : D.IsStandard F) :
    ∃! φ : Module.End ℤ (Fin t.rank → ℤ), IsCharacterMap (D.torusPoints K) F φ :=
  let ⟨φ, _, hφ⟩ := hF.exists_isCharacterMap
  ⟨φ, hφ, fun _ hψ => (hφ.unique (D.torusPoints_injective K) hψ).symm⟩

/-- **The unique character map of a standard endomorphism** on `D.torusPoints K`. -/
noncomputable def IsStandard.characterMap (hF : D.IsStandard F) : Module.End ℤ (Fin t.rank → ℤ) :=
  hF.existsUnique_characterMap.choose

/-- A standard endomorphism acts on `D.torusPoints K` through `hF.characterMap`. -/
theorem IsStandard.isCharacterMap (hF : D.IsStandard F) :
    IsCharacterMap (D.torusPoints K) F hF.characterMap := hF.existsUnique_characterMap.choose_spec.1

/-- Any character map of `F` on `D.torusPoints K` equals `hF.characterMap`. -/
theorem IsStandard.characterMap_eq_of_isCharacterMap (hF : D.IsStandard F)
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ) :
    hF.characterMap = φ := (hF.existsUnique_characterMap.choose_spec.2 φ hφ).symm

/-- Congruence of `characterMap` along an equality of standard endomorphisms. -/
theorem IsStandard.characterMap_congr (h : F = F') (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    hF.characterMap = hF'.characterMap := by
  subst h; rfl

/-- The character map of a standard endomorphism is injective. -/
theorem IsStandard.characterMap_injective (hF : D.IsStandard F) :
    Function.Injective hF.characterMap :=
  let ⟨_, hφ_inj, hφ⟩ := hF.exists_isCharacterMap
  (hF.characterMap_eq_of_isCharacterMap hφ).symm ▸ hφ_inj

/-- The character map of the identity endomorphism is `1`. -/
@[simp] theorem IsStandard.characterMap_id : (D.isStandard_id (A := K)).characterMap = 1 :=
  (D.isStandard_id (A := K)).characterMap_eq_of_isCharacterMap (isCharacterMap_id _)

/-- Character maps are contravariant under composition of standard endomorphisms. -/
@[simp] theorem IsStandard.characterMap_comp (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    (hF.comp hF').characterMap = hF'.characterMap * hF.characterMap :=
  (hF.comp hF').characterMap_eq_of_isCharacterMap (hF.isCharacterMap.comp hF'.isCharacterMap)

/-- The character map of `F ^ n` in `Monoid.End` is `hF.characterMap ^ n`. -/
@[simp] theorem IsStandard.characterMap_pow {F : Monoid.End (D.points K)} (hF : D.IsStandard F)
    (n : ℕ) : (hF.pow n).characterMap = hF.characterMap ^ n :=
  (hF.pow n).characterMap_eq_of_isCharacterMap (hF.isCharacterMap.pow n)

/-- The character map of `D.frobenius p k K` is `(p ^ k : ℕ) • 1`. -/
@[simp] theorem IsStandard.characterMap_frobenius (p k : ℕ) [ExpChar K p] [PerfectRing K p] :
    (D.isStandard_frobenius (A := K) p k).characterMap = (p ^ k : ℕ) • 1 :=
  (D.isStandard_frobenius p k).characterMap_eq_of_isCharacterMap (D.isCharacterMap_frobenius p k K)

private theorem IsStandard.paramHomOf_torusCharacter_mul (hF : D.IsStandard F)
    {α β : Fin t.numRoots}
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range)
    (s : Fin t.rank → Kˣ) (u : K) :
    hF.paramHomOf α β hβ ((torusCharacter s (D.coordinateRoot α) : K) * u) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot β)) : K) *
        hF.paramHomOf α β hβ u := by
  have hconj := congrArg F (D.torusPoints_conj_rootSubgroupPoints α K s u)
  rw [map_mul, map_mul, map_inv, ← hF.rootSubgroupPoints_paramHomOf hβ,
    ← hF.rootSubgroupPoints_paramHomOf hβ, hF.isCharacterMap.map_apply,
    D.torusPoints_conj_rootSubgroupPoints, torusCharacter_torusPointMap] at hconj
  simpa only [toAdd_ofAdd] using congrArg toAdd (D.rootSubgroupPoints_injective K _ hconj.symm)

private theorem nsmul_eq_nsmul_of_nsmul_eq {M : Type*} [AddCommMonoid M]
    {d₁ m₁ d₂ m₂ : ℕ} {x y₁ y₂ : M}
    (h₁ : d₁ • x = m₁ • y₁) (h₂ : d₂ • x = m₂ • y₂) :
    (d₂ * m₁) • y₁ = (d₁ * m₂) • y₂ := by
  rw [mul_smul, ← h₁, smul_comm, h₂, ← mul_smul]

private theorem IsStandard.rawRootMap_injective (hF : D.IsStandard F) :
    Function.Injective hF.rawRootMap := fun α₁ α₂ hβ => by
  have hrel (α) := AddMonoidHom.exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_mul
    (hF.paramHomOf α (hF.rawRootMap α) (hF.map_range_rootSubgroupPoints_rawRootMap α))
    (hF.paramHomOf_ne_zero (hF.map_range_rootSubgroupPoints_rawRootMap α))
    (hF.paramHomOf_torusCharacter_mul (hF.map_range_rootSubgroupPoints_rawRootMap α))
  obtain ⟨d₁, m₁, _, hm₁, hrel₁⟩ := hrel α₁; obtain ⟨d₂, m₂, hd₂, _, hrel₂⟩ := hrel α₂
  rw [hβ] at hrel₁
  exact D.eq_of_nsmul_coordinateRoot_eq (Nat.mul_pos hd₂ hm₁)
    (nsmul_eq_nsmul_of_nsmul_eq hrel₁ hrel₂)

/-- **The root permutation `σ : Equiv.Perm (Fin t.numRoots)` of a standard endomorphism.** -/
noncomputable def IsStandard.rootPerm (hF : D.IsStandard F) : Equiv.Perm (Fin t.numRoots) :=
  Equiv.ofBijective hF.rawRootMap (Finite.injective_iff_bijective.mp hF.rawRootMap_injective)

private theorem IsStandard.rootPerm_apply (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.rootPerm α = hF.rawRootMap α := Equiv.ofBijective_apply _ _ α

/-- A standard endomorphism maps the `α`-root subgroup onto the `hF.rootPerm α`-root subgroup. -/
theorem IsStandard.map_range_rootSubgroupPoints (hF : D.IsStandard F) (α : Fin t.numRoots) :
    (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints (hF.rootPerm α) K).range := by
  rw [hF.rootPerm_apply]; exact hF.map_range_rootSubgroupPoints_rawRootMap α

/-- Recognition lemma for `hF.rootPerm` from the image of a root subgroup. -/
theorem IsStandard.rootPerm_eq_of_map_range (hF : D.IsStandard F) {α β : Fin t.numRoots}
    (h : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) :
    hF.rootPerm α = β :=
  D.range_rootSubgroupPoints_injective K ((hF.map_range_rootSubgroupPoints α).symm.trans h)

/-- Congruence of `rootPerm` along an equality of standard endomorphisms. -/
theorem IsStandard.rootPerm_congr (h : F = F') (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    hF.rootPerm = hF'.rootPerm := by
  subst h; rfl

/-- **The additive parameter map `K →+ K` of a standard endomorphism on the `α`-root subgroup**,
satisfying `x_{hF.rootPerm α}(hF.rootParamHom α u) = F (x_α(u))`. -/
noncomputable def IsStandard.rootParamHom (hF : D.IsStandard F) (α : Fin t.numRoots) : K →+ K :=
  hF.paramHomOf α (hF.rootPerm α) (hF.map_range_rootSubgroupPoints α)

/-- Pointwise action of a standard endomorphism on a root subgroup via `hF.rootParamHom`. -/
theorem IsStandard.rootSubgroupPoints_rootParamHom (hF : D.IsStandard F) (α : Fin t.numRoots)
    (u : K) :
    D.rootSubgroupPoints (hF.rootPerm α) K (ofAdd (hF.rootParamHom α u)) =
      F (D.rootSubgroupPoints α K (ofAdd u)) :=
  hF.rootSubgroupPoints_paramHomOf (hF.map_range_rootSubgroupPoints α) u

/-- Recognition lemma for `hF.rootParamHom α` from its action on `D.rootSubgroupPoints α K`. -/
theorem IsStandard.rootParamHom_eq_of_map_rootSubgroupPoints (hF : D.IsStandard F)
    {α : Fin t.numRoots} {f : K →+ K}
    (h : ∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints (hF.rootPerm α) K (ofAdd (f u))) :
    hF.rootParamHom α = f := AddMonoidHom.ext fun u => by
  simpa only [toAdd_ofAdd] using congrArg toAdd
    (D.rootSubgroupPoints_injective K _ ((hF.rootSubgroupPoints_rootParamHom α u).trans (h u)))

/-- Congruence of `rootParamHom` along an equality of standard endomorphisms. -/
theorem IsStandard.rootParamHom_congr (h : F = F') (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    hF.rootParamHom = hF'.rootParamHom := by
  subst h; rfl

/-- Each additive root-parameter map `hF.rootParamHom α` is surjective. -/
theorem IsStandard.rootParamHom_surjective (hF : D.IsStandard F) (α : Fin t.numRoots) :
    Function.Surjective (hF.rootParamHom α) :=
  hF.paramHomOf_surjective (hF.map_range_rootSubgroupPoints α)

/-- Each additive root-parameter map `hF.rootParamHom α` is nonzero. -/
theorem IsStandard.rootParamHom_ne_zero (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.rootParamHom α ≠ 0 :=
  hF.paramHomOf_ne_zero (hF.map_range_rootSubgroupPoints α)

/-- Torus-character intertwining of `hF.rootParamHom α`. -/
theorem IsStandard.rootParamHom_torusCharacter_mul (hF : D.IsStandard F)
    (α : Fin t.numRoots) (s : Fin t.rank → Kˣ) (u : K) :
    hF.rootParamHom α ((torusCharacter s (D.coordinateRoot α) : K) * u) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot (hF.rootPerm α))) : K) *
        hF.rootParamHom α u :=
  hF.paramHomOf_torusCharacter_mul (hF.map_range_rootSubgroupPoints α) s u

/-- **Positive rational proportionality on coordinate roots**:
`d • φ (D.coordinateRoot (σ α)) = m • D.coordinateRoot α` with `0 < d` and `0 < m`. -/
theorem IsStandard.exists_pos_nsmul_characterMap_coordinateRoot (hF : D.IsStandard F)
    (α : Fin t.numRoots) : ∃ d m : ℕ, 0 < d ∧ 0 < m ∧
      d • hF.characterMap (D.coordinateRoot (hF.rootPerm α)) = m • D.coordinateRoot α :=
  (hF.rootParamHom α).exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_mul
    (hF.rootParamHom_ne_zero α) (hF.rootParamHom_torusCharacter_mul α)

/-- **The root permutation of a standard endomorphism commutes with root negation.** -/
@[simp] theorem IsStandard.rootPerm_reflectionPerm_self (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.rootPerm ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
      (t.simplyConnectedRootDatum ht).reflectionPerm (hF.rootPerm α) (hF.rootPerm α) := by
  obtain ⟨d₁, m₁, _, hm₁, hrel₁⟩ := hF.exists_pos_nsmul_characterMap_coordinateRoot α
  obtain ⟨d₂, m₂, hd₂, _, hrel₂⟩ := hF.exists_pos_nsmul_characterMap_coordinateRoot
    ((t.simplyConnectedRootDatum ht).reflectionPerm α α)
  have hrel₁' : m₁ • (-D.coordinateRoot α) =
      d₁ • hF.characterMap (D.coordinateRoot
        ((t.simplyConnectedRootDatum ht).reflectionPerm (hF.rootPerm α) (hF.rootPerm α))) := by
    rw [D.coordinateRoot_reflectionPerm_self, map_neg, smul_neg, smul_neg, hrel₁]
  have hrel₂' : m₂ • (-D.coordinateRoot α) =
      d₂ • hF.characterMap (D.coordinateRoot
        (hF.rootPerm ((t.simplyConnectedRootDatum ht).reflectionPerm α α))) := by
    rw [← D.coordinateRoot_reflectionPerm_self, hrel₂.symm]
  have hcross := nsmul_eq_nsmul_of_nsmul_eq hrel₂' hrel₁'
  rw [← map_nsmul, ← map_nsmul] at hcross
  exact D.eq_of_nsmul_coordinateRoot_eq (Nat.mul_pos hm₁ hd₂) (hF.characterMap_injective hcross)

/-- **Two standard endomorphisms with equal character maps induce the same root permutation.** -/
theorem IsStandard.rootPerm_eq_of_characterMap_eq (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (hφ : hF.characterMap = hF'.characterMap) : hF.rootPerm = hF'.rootPerm := Equiv.ext fun α => by
  obtain ⟨d, m, hd, _, hrel⟩ := hF.exists_pos_nsmul_characterMap_coordinateRoot α
  obtain ⟨d', m', _, hm', hrel'⟩ := hF'.exists_pos_nsmul_characterMap_coordinateRoot α
  rw [hφ] at hrel
  have hcross := nsmul_eq_nsmul_of_nsmul_eq hrel.symm hrel'.symm
  rw [← map_nsmul, ← map_nsmul] at hcross
  exact D.eq_of_nsmul_coordinateRoot_eq (Nat.mul_pos hm' hd) (hF'.characterMap_injective hcross)

/-- **Two standard endomorphisms sharing a character map `φ` induce the same root permutation.** -/
theorem IsStandard.rootPerm_eq_of_isCharacterMap (hF : D.IsStandard F) (hF' : D.IsStandard F')
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hφ' : IsCharacterMap (D.torusPoints K) F' φ) : hF.rootPerm = hF'.rootPerm :=
  hF.rootPerm_eq_of_characterMap_eq hF' ((hF.characterMap_eq_of_isCharacterMap hφ).trans
    (hF'.characterMap_eq_of_isCharacterMap hφ').symm)

/-- A standard endomorphism is based iff its root permutation preserves positive roots. -/
theorem IsStandard.isBased_iff_forall_rootPerm_mem_posRoots (hF : D.IsStandard F) :
    D.IsBased F ↔ ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      hF.rootPerm α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
  ⟨fun hB α hα => by
      obtain ⟨β, hβpos, hβ⟩ := hB.exists_map_range_rootSubgroupPoints hα
      rwa [hF.rootPerm_eq_of_map_range hβ],
    fun hpos => ⟨hF, fun α hα => ⟨hF.rootPerm α, hpos α hα, hF.map_range_rootSubgroupPoints α⟩⟩⟩

/-- For a based endomorphism, `rootPerm` preserves positive roots. -/
theorem IsBased.rootPerm_mem_posRoots (hF : D.IsBased F) {α : Fin t.numRoots}
    (hα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    hF.isStandard.rootPerm α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
  (hF.isStandard.isBased_iff_forall_rootPerm_mem_posRoots.mp hF) α hα

/-- For a based endomorphism, `rootPerm` maps `posRoots` bijectively onto itself. -/
@[simp] theorem IsBased.image_rootPerm_posRoots (hF : D.IsBased F) :
    hF.isStandard.rootPerm '' posRoots (t.rationalRootSystem ht) (t.rationalBase ht) =
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
  (((Set.toFinite _).injOn_iff_bijOn_of_mapsTo fun _ hα => hF.rootPerm_mem_posRoots hα).mp
    hF.isStandard.rootPerm.injective.injOn).image_eq

/-- Over an infinite field, a based endomorphism maps `D.positivePoints K` onto itself. -/
theorem IsBased.map_positivePoints_eq (hF : D.IsBased F) :
    (D.positivePoints K).map F = D.positivePoints K := by
  refine le_antisymm hF.map_positivePoints_le (D.positivePoints_le_iff.mpr fun β hβ u => ?_)
  have hα : hF.isStandard.rootPerm.symm β ∈
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    obtain ⟨α, hα, hβα⟩ := hF.image_rootPerm_posRoots.symm ▸ hβ
    rw [hF.isStandard.rootPerm.symm_apply_eq.mpr hβα.symm]
    exact hα
  have hmem : D.rootSubgroupPoints β K u ∈
      (D.rootSubgroupPoints (hF.isStandard.rootPerm.symm β) K).range.map F := by
    rw [hF.isStandard.map_range_rootSubgroupPoints, Equiv.apply_symm_apply]
    exact ⟨u, rfl⟩
  exact Subgroup.map_mono
    (show (D.rootSubgroupPoints (hF.isStandard.rootPerm.symm β) K).range ≤ D.positivePoints K from
      by rintro _ ⟨v, rfl⟩; exact D.rootSubgroupPoints_mem_positivePoints K hα v) hmem

/-- For a based endomorphism, `rootPerm α` is positive iff `α` is positive. -/
-- Note: `@[simp]` is on `isPos_rootPerm_iff` because `TauCeti.mem_posRoots` simplifies
-- `∈ posRoots ...` to `(t.rationalBase ht).IsPos`.
theorem IsBased.rootPerm_mem_posRoots_iff (hF : D.IsBased F) {α : Fin t.numRoots} :
    hF.isStandard.rootPerm α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
  ⟨fun h => let ⟨_, hβ, hβα⟩ := hF.image_rootPerm_posRoots.symm ▸ h
    hF.isStandard.rootPerm.injective hβα ▸ hβ, hF.rootPerm_mem_posRoots⟩

/-- For a based endomorphism, `(t.rationalBase ht).IsPos (rootPerm α)` iff `α` is positive. -/
@[simp] theorem IsBased.isPos_rootPerm_iff (hF : D.IsBased F) {α : Fin t.numRoots} :
    (t.rationalBase ht).IsPos (hF.isStandard.rootPerm α) ↔ (t.rationalBase ht).IsPos α := by
  simp only [← mem_posRoots]
  exact hF.rootPerm_mem_posRoots_iff

/-- The root permutation of the identity endomorphism is `1`. -/
@[simp] theorem IsStandard.rootPerm_id : (D.isStandard_id (A := K)).rootPerm = 1 :=
  Equiv.ext fun _ => (D.isStandard_id (A := K)).rootPerm_eq_of_map_range (Subgroup.map_id _)

/-- Root permutations are covariant under composition of standard endomorphisms. -/
@[simp] theorem IsStandard.rootPerm_comp (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    (hF.comp hF').rootPerm = hF.rootPerm * hF'.rootPerm :=
  Equiv.ext fun α => (hF.comp hF').rootPerm_eq_of_map_range (by
    rw [← Subgroup.map_map, hF'.map_range_rootSubgroupPoints, hF.map_range_rootSubgroupPoints,
      Equiv.Perm.mul_apply])

/-- The root permutation of `F ^ n` in `Monoid.End` is `hF.rootPerm ^ n`. -/
@[simp] theorem IsStandard.rootPerm_pow {F : Monoid.End (D.points K)} (hF : D.IsStandard F)
    (n : ℕ) : (hF.pow n).rootPerm = hF.rootPerm ^ n := by
  induction n with
  | zero => exact Equiv.ext fun _ => (hF.pow 0).rootPerm_eq_of_map_range (by
      rw [pow_zero, Monoid.End.one_eq_id, Subgroup.map_id, pow_zero, Equiv.Perm.one_apply])
  | succ n ih => exact (Equiv.ext fun α => (hF.pow (n + 1)).rootPerm_eq_of_map_range (by
      rw [pow_succ', Monoid.End.mul_eq_comp]
      exact (hF.comp (hF.pow n)).map_range_rootSubgroupPoints α)).trans
                  ((IsStandard.rootPerm_comp hF (hF.pow n)).trans (by rw [ih, pow_succ']))

/-- The root permutation of `D.frobenius p k K` is `1`. -/
@[simp] theorem IsStandard.rootPerm_frobenius (p k : ℕ) [ExpChar K p] [PerfectRing K p] :
    (D.isStandard_frobenius (A := K) p k).rootPerm = 1 :=
  Equiv.ext fun α => (D.isStandard_frobenius p k).rootPerm_eq_of_map_range
    (D.map_range_rootSubgroupPoints_frobenius p k K α)

/-- The additive root-parameter map of the identity endomorphism is `AddMonoidHom.id K`. -/
@[simp] theorem IsStandard.rootParamHom_id (α : Fin t.numRoots) :
    (D.isStandard_id (A := K)).rootParamHom α = AddMonoidHom.id K :=
  (D.isStandard_id (A := K)).rootParamHom_eq_of_map_rootSubgroupPoints fun _ => by simp

/-- Additive root-parameter maps are covariant under composition of standard endomorphisms. -/
@[simp] theorem IsStandard.rootParamHom_comp (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (α : Fin t.numRoots) :
    (hF.comp hF').rootParamHom α =
      (hF.rootParamHom (hF'.rootPerm α)).comp (hF'.rootParamHom α) :=
  (hF.comp hF').rootParamHom_eq_of_map_rootSubgroupPoints fun u => by
    rw [MonoidHom.comp_apply, ← hF'.rootSubgroupPoints_rootParamHom,
      ← hF.rootSubgroupPoints_rootParamHom, AddMonoidHom.comp_apply,
      IsStandard.rootPerm_comp, Equiv.Perm.mul_apply]

/-- The additive root-parameter map of `D.frobenius p k K` is `iterateFrobenius K p k`. -/
@[simp] theorem IsStandard.rootParamHom_frobenius (p k : ℕ) [ExpChar K p] [PerfectRing K p]
    (α : Fin t.numRoots) :
    (D.isStandard_frobenius (A := K) p k).rootParamHom α =
      (iterateFrobenius K p k).toAddMonoidHom :=
  (D.isStandard_frobenius p k).rootParamHom_eq_of_map_rootSubgroupPoints fun _ => by
    simp [iterateFrobenius_def]

/-! ## Scaling units and field endomorphisms over an infinite field with divisible units -/

variable [RootableBy Kˣ ℕ]

/-- Over an infinite field with divisible units, a standard endomorphism maps
`D.rootTorusSubgroup K` onto itself. -/
theorem IsStandard.map_rootTorusSubgroup_eq (hF : D.IsStandard F) :
    (D.rootTorusSubgroup K).map F = D.rootTorusSubgroup K := by
  refine le_antisymm hF.map_rootTorusSubgroup_le ((D.rootTorusSubgroup_le_iff K _).mpr ⟨?_, ?_⟩)
  · intro β u
    have hmem : D.rootSubgroupPoints β K u ∈
        (D.rootSubgroupPoints (hF.rootPerm.symm β) K).range.map F := by
      rw [hF.map_range_rootSubgroupPoints, Equiv.apply_symm_apply]
      exact ⟨u, rfl⟩
    exact Subgroup.map_mono
      (show (D.rootSubgroupPoints (hF.rootPerm.symm β) K).range ≤ D.rootTorusSubgroup K from
        by rintro _ ⟨v, rfl⟩; exact D.rootSubgroupPoints_mem_rootTorusSubgroup _ K v) hmem
  · intro s
    have hmem : D.torusPoints K s ∈ (D.torusPoints K).range.map F := by
      rw [hF.map_range_torusPoints_eq]
      exact ⟨s, rfl⟩
    exact Subgroup.map_mono
      (show (D.torusPoints K).range ≤ D.rootTorusSubgroup K from
        by rintro _ ⟨s', rfl⟩; exact D.torusPoints_mem_rootTorusSubgroup K s') hmem

/-- Over an infinite field with divisible units, a based endomorphism maps
`D.borelSubgroup K` onto itself. -/
theorem IsBased.map_borelSubgroup_eq (hF : D.IsBased F) :
    (D.borelSubgroup K).map F = D.borelSubgroup K := by
  rw [D.borelSubgroup_def, Subgroup.map_sup, hF.map_positivePoints_eq,
    hF.isStandard.map_range_torusPoints_eq]

private theorem IsStandard.rootParamHom_one_ne_zero (hF : D.IsStandard F) (α) :
    hF.rootParamHom α 1 ≠ 0 := fun h0 => by
  obtain ⟨u, hu⟩ := hF.rootParamHom_surjective α 1
  by_cases hu0 : u = 0; · exact (@one_ne_zero K _ _) (by simpa [hu0] using hu.symm)
  obtain ⟨s, hs⟩ := torusCharacter_surjective (D.coordinateRoot_ne_zero α) (Units.mk0 u hu0)
  have hs' : (torusCharacter s (D.coordinateRoot α) : K) = u := by simpa using congrArg Units.val hs
  exact (@one_ne_zero K _ _)
    (hu.symm.trans (by simpa [hs', h0] using hF.rootParamHom_torusCharacter_mul α s 1))

/-- **The field endomorphism `g_α : K →+* K` of a standard endomorphism on the `α`-root subgroup**,
normalized by `F (x_α(u)) = x_{hF.rootPerm α}(hF.rootUnit α * g_α u)`. -/
noncomputable def IsStandard.fieldEnd (hF : D.IsStandard F) (α : Fin t.numRoots) : K →+* K :=
  (AddMonoidHom.mk' (fun u => (hF.rootParamHom α 1)⁻¹ * hF.rootParamHom α u) fun _ _ => by
      rw [map_add, mul_add]).toRingHomOfTorusCharacter
    (torusCharacter_surjective (D.coordinateRoot_ne_zero α))
    (by simp [inv_mul_cancel₀ (hF.rootParamHom_one_ne_zero α)])
    (fun s u => by simp only [AddMonoidHom.mk'_apply, hF.rootParamHom_torusCharacter_mul]; ring)

/-- Explicit formula for `hF.fieldEnd α` in terms of `hF.rootParamHom α`. -/
theorem IsStandard.fieldEnd_apply_eq (hF : D.IsStandard F) (α : Fin t.numRoots) (u : K) :
    hF.fieldEnd α u = (hF.rootParamHom α 1)⁻¹ * hF.rootParamHom α u := by
  rw [IsStandard.fieldEnd, AddMonoidHom.toRingHomOfTorusCharacter_apply, AddMonoidHom.mk'_apply]

/-- Congruence of `fieldEnd` along an equality of standard endomorphisms. -/
theorem IsStandard.fieldEnd_congr (h : F = F') (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    hF.fieldEnd = hF'.fieldEnd := by
  subst h; rfl

/-- Each root-subgroup field endomorphism `hF.fieldEnd α` is bijective. -/
theorem IsStandard.fieldEnd_bijective (hF : D.IsStandard F) (α : Fin t.numRoots) :
    Function.Bijective (hF.fieldEnd α) := ⟨(hF.fieldEnd α).injective, fun y => by
  obtain ⟨u, hu⟩ := hF.rootParamHom_surjective α (hF.rootParamHom α 1 * y)
  exact ⟨u, by rw [hF.fieldEnd_apply_eq, hu, inv_mul_cancel_left₀ (hF.rootParamHom_one_ne_zero α)]⟩⟩

/-- **The field automorphism `K ≃+* K` of a standard endomorphism on the `α`-root subgroup**,
bundling `hF.fieldEnd α` with its bijectivity. -/
noncomputable def IsStandard.fieldEquiv (hF : D.IsStandard F) (α : Fin t.numRoots) : K ≃+* K :=
  RingEquiv.ofBijective (hF.fieldEnd α) (hF.fieldEnd_bijective α)

/-- The underlying ring homomorphism of `hF.fieldEquiv α` is `hF.fieldEnd α`. -/
@[simp] theorem IsStandard.toRingHom_fieldEquiv (hF : D.IsStandard F) (α : Fin t.numRoots) :
    (hF.fieldEquiv α : K →+* K) = hF.fieldEnd α := (rfl)

/-- Pointwise evaluation of `hF.fieldEquiv α` equals `hF.fieldEnd α`. -/
@[simp] theorem IsStandard.fieldEquiv_apply (hF : D.IsStandard F) (α : Fin t.numRoots) (u : K) :
    hF.fieldEquiv α u = hF.fieldEnd α u := (rfl)

/-- **The scaling unit `c_α : Kˣ` of a standard endomorphism on the `α`-root subgroup**, defined by
`F (x_α(1)) = x_{hF.rootPerm α}(c_α)` (`IsStandard.map_rootSubgroupPoints`). -/
noncomputable def IsStandard.rootUnit (hF : D.IsStandard F) (α : Fin t.numRoots) : Kˣ :=
  Units.mk0 (hF.rootParamHom α 1) (hF.rootParamHom_one_ne_zero α)

/-- Coercion of `hF.rootUnit α` to `K` equals `hF.rootParamHom α 1`. -/
@[simp] theorem IsStandard.coe_rootUnit (hF : D.IsStandard F) (α : Fin t.numRoots) :
    (hF.rootUnit α : K) = hF.rootParamHom α 1 := Units.val_mk0 _

/-- Congruence of `rootUnit` along an equality of standard endomorphisms. -/
theorem IsStandard.rootUnit_congr (h : F = F') (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    hF.rootUnit = hF'.rootUnit := by
  subst h; rfl

/-- **Explicit root-subgroup formula**: `F (x_α(u)) = x_{σ α}(c_α * g_α u)`. -/
theorem IsStandard.map_rootSubgroupPoints (hF : D.IsStandard F) (α : Fin t.numRoots) (u : K) :
    F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints (hF.rootPerm α) K (ofAdd ((hF.rootUnit α : K) * hF.fieldEnd α u)) := by
  rw [IsStandard.coe_rootUnit, hF.fieldEnd_apply_eq,
    mul_inv_cancel_left₀ (hF.rootParamHom_one_ne_zero α)]
  exact (hF.rootSubgroupPoints_rootParamHom α u).symm

/-- Over an infinite field with divisible units, `hF.rootParamHom α` acts by scaling
`hF.fieldEnd α` by `hF.rootUnit α`. -/
theorem IsStandard.rootParamHom_apply_eq_mul_fieldEnd (hF : D.IsStandard F)
    (α : Fin t.numRoots) (u : K) :
    hF.rootParamHom α u = (hF.rootUnit α : K) * hF.fieldEnd α u := by
  simpa only [toAdd_ofAdd] using congrArg toAdd (D.rootSubgroupPoints_injective K _
    ((hF.rootSubgroupPoints_rootParamHom α u).trans (hF.map_rootSubgroupPoints α u)))

/-- **Intertwining of `hF.fieldEnd α` with torus characters.** -/
@[simp] theorem IsStandard.fieldEnd_torusCharacter (hF : D.IsStandard F) (α : Fin t.numRoots)
    (s : Fin t.rank → Kˣ) : hF.fieldEnd α (torusCharacter s (D.coordinateRoot α) : K) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot (hF.rootPerm α))) : K) :=
  AddMonoidHom.toRingHomOfTorusCharacter_torusCharacter _ _ _ _ s

/-- **Uniqueness of `(hF.rootPerm α, hF.rootUnit α, hF.fieldEnd α)`** from
`F (x_α(u)) = x_β(c * g u)`. -/
theorem IsStandard.eq_of_map_rootSubgroupPoints (hF : D.IsStandard F) {α β : Fin t.numRoots}
    {c : Kˣ} {g : K →+* K} (h : ∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints β K (ofAdd ((c : K) * g u))) :
    β = hF.rootPerm α ∧ c = hF.rootUnit α ∧ g = hF.fieldEnd α := by
  obtain rfl : β = hF.rootPerm α := ((D.range_rootSubgroupPoints_le_iff K).mp (by
    rw [← hF.map_range_rootSubgroupPoints α]; rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨ofAdd ((c : K) * g (toAdd u)), by conv_rhs => rw [← ofAdd_toAdd u, h]⟩)).symm
  have hparam (u : K) : (c : K) * g u = (hF.rootUnit α : K) * hF.fieldEnd α u := by
    simpa only [toAdd_ofAdd] using congrArg toAdd
      (D.rootSubgroupPoints_injective K _ ((h u).symm.trans (hF.map_rootSubgroupPoints α u)))
  obtain rfl : c = hF.rootUnit α := Units.ext (by simpa using hparam 1)
  exact ⟨rfl, rfl, RingHom.ext fun u => mul_left_cancel₀ (Units.ne_zero _) (hparam u)⟩

/-- **Opposite roots carry the same field endomorphism.** -/
@[simp] theorem IsStandard.fieldEnd_reflectionPerm_self (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.fieldEnd ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = hF.fieldEnd α :=
  eq_of_map_torusCharacter_eq (torusCharacter_surjective (D.coordinateRoot_ne_zero α)) fun s => by
    have hneg := hF.fieldEnd_torusCharacter ((t.simplyConnectedRootDatum ht).reflectionPerm α α) s
    simp only [D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, Units.val_inv_eq_inv_val,
      map_inv₀, IsStandard.rootPerm_reflectionPerm_self, map_neg, inv_inj] at hneg
    exact hneg.trans (hF.fieldEnd_torusCharacter α s).symm

/-- **Two standard endomorphisms with equal character maps induce the same field endomorphism.** -/
theorem IsStandard.fieldEnd_eq_of_characterMap_eq (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (hφ : hF.characterMap = hF'.characterMap) (α : Fin t.numRoots) :
    hF.fieldEnd α = hF'.fieldEnd α :=
  eq_of_map_torusCharacter_eq (torusCharacter_surjective (D.coordinateRoot_ne_zero α)) fun s => by
    rw [hF.fieldEnd_torusCharacter, hF'.fieldEnd_torusCharacter, hφ,
      hF.rootPerm_eq_of_characterMap_eq hF' hφ]

/-- **Two standard endomorphisms sharing a character map induce the same field endomorphism.** -/
theorem IsStandard.fieldEnd_eq_of_isCharacterMap (hF : D.IsStandard F) (hF' : D.IsStandard F')
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hφ' : IsCharacterMap (D.torusPoints K) F' φ) (α : Fin t.numRoots) :
    hF.fieldEnd α = hF'.fieldEnd α :=
  hF.fieldEnd_eq_of_characterMap_eq hF' ((hF.characterMap_eq_of_isCharacterMap hφ).trans
    (hF'.characterMap_eq_of_isCharacterMap hφ').symm) α

/-- The scaling unit of the identity endomorphism is `1`. -/
@[simp] theorem IsStandard.rootUnit_id (α : Fin t.numRoots) :
    (D.isStandard_id (A := K)).rootUnit α = 1 :=
  ((D.isStandard_id (A := K)).eq_of_map_rootSubgroupPoints (β := α) (c := 1) (g := RingHom.id K)
    fun _ => by simp).2.1.symm

/-- The field endomorphism of the identity endomorphism is `RingHom.id K`. -/
@[simp] theorem IsStandard.fieldEnd_id (α : Fin t.numRoots) :
    (D.isStandard_id (A := K)).fieldEnd α = RingHom.id K :=
  ((D.isStandard_id (A := K)).eq_of_map_rootSubgroupPoints (β := α) (c := 1) (g := RingHom.id K)
    fun _ => by simp).2.2.symm

private theorem IsStandard.comp_invariants (hF : D.IsStandard F) (hF' : D.IsStandard F') (α) :
    hF.rootUnit (hF'.rootPerm α) * Units.map (hF.fieldEnd (hF'.rootPerm α)).toMonoidHom
      (hF'.rootUnit α) = (hF.comp hF').rootUnit α ∧
      (hF.fieldEnd (hF'.rootPerm α)).comp (hF'.fieldEnd α) = (hF.comp hF').fieldEnd α :=
  ((hF.comp hF').eq_of_map_rootSubgroupPoints (β := hF.rootPerm (hF'.rootPerm α)) fun _ => by
    simp [hF'.map_rootSubgroupPoints, hF.map_rootSubgroupPoints, mul_assoc]).2

/-- Scaling unit of a composition of standard endomorphisms. -/
@[simp] theorem IsStandard.rootUnit_comp (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (α : Fin t.numRoots) : (hF.comp hF').rootUnit α = hF.rootUnit (hF'.rootPerm α) *
      Units.map (hF.fieldEnd (hF'.rootPerm α)).toMonoidHom (hF'.rootUnit α) :=
  (hF.comp_invariants hF' α).1.symm

/-- Field endomorphism of a composition of standard endomorphisms. -/
@[simp] theorem IsStandard.fieldEnd_comp (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (α : Fin t.numRoots) : (hF.comp hF').fieldEnd α =
      (hF.fieldEnd (hF'.rootPerm α)).comp (hF'.fieldEnd α) := (hF.comp_invariants hF' α).2.symm

/-- The scaling unit of `D.frobenius p k K` is `1`. -/
@[simp] theorem IsStandard.rootUnit_frobenius (p k : ℕ) [ExpChar K p] [PerfectRing K p]
    (α : Fin t.numRoots) : (D.isStandard_frobenius (A := K) p k).rootUnit α = 1 :=
  ((D.isStandard_frobenius p k).eq_of_map_rootSubgroupPoints (β := α) (c := 1)
    (g := iterateFrobenius K p k) fun _ => by simp [iterateFrobenius_def]).2.1.symm

/-- The field endomorphism of `D.frobenius p k K` is `iterateFrobenius K p k`. -/
@[simp] theorem IsStandard.fieldEnd_frobenius (p k : ℕ) [ExpChar K p] [PerfectRing K p]
    (α : Fin t.numRoots) : (D.isStandard_frobenius (A := K) p k).fieldEnd α =
      iterateFrobenius K p k :=
  ((D.isStandard_frobenius p k).eq_of_map_rootSubgroupPoints (β := α) (c := 1)
    (g := iterateFrobenius K p k) fun _ => by simp [iterateFrobenius_def]).2.2.symm

end Field
end TauCeti.DynkinType.ChevalleyDatum
