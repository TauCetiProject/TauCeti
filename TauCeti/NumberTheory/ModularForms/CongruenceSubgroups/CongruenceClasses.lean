/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Congruence classes of characters of subgroups of `SL(2, ℤ)`

Let `Γ` be a subgroup of `SL(2, ℤ)` and `A` a module over a semiring `R`. A character
`ψ : Γ → A` (an additive character, that is a homomorphism `Additive Γ →+ A`) is a
**congruence class** when it vanishes on `Γ ∩ Γ(m)` for some positive level `m`, where `Γ(m)` is
the principal congruence subgroup. Equivalently, `ψ` factors through one of the finite congruence
quotients `Γ ⧸ (Γ ∩ Γ(m))`. The congruence classes form a submodule
`CongruenceSubgroup.congruenceClasses Γ R A`: two characters vanishing at levels `m₁` and `m₂`
both vanish at level `lcm m₁ m₂`.

For `Γ = Γ(N)` and `A = 𝔽_q` with the trivial action, characters are the classes of ordinary
cohomology `H¹(Γ(N), 𝔽_q)`, and the congruence classes are the subspace `H¹_cong(Γ(N), 𝔽_q)` of
Calegari–Dimitrov–Tang. Ihara-type theorems at principal level do not assert that the
difference of the two degeneracy restrictions is injective on `H¹`; they assert that its kernel
consists of congruence classes, which is where this subspace is used. It is not all of `H¹`:
for `Γ(3)` and `𝔽₅` coefficients it is zero while `H¹` is not (Calegari–Dimitrov–Tang, §4.5).

## Main definitions

* `CongruenceSubgroup.congruenceClassesOfLevel Γ R A m`: the characters of `Γ` vanishing on
  `Γ ∩ Γ(m)`.
* `CongruenceSubgroup.congruenceClasses Γ R A`: the characters of `Γ` vanishing on `Γ ∩ Γ(m)` for
  some `m > 0`.
* `CongruenceSubgroup.congruenceClassesOfLevelEquiv Γ R A m`: characters of level `m` are the
  characters of the congruence quotient `Γ ⧸ (Γ ∩ Γ(m))`, which is finite for `m ≠ 0`.
* `CongruenceSubgroup.congruenceClassesH1 Γ A`: for a trivial representation `A` of `Γ`, the
  congruence classes in `H¹(Γ, A)`, transported along `groupCohomology.H1IsoOfIsTrivial`.

## Main results

* `CongruenceSubgroup.congruenceClassesOfLevel_le_of_dvd`: a character of level `m` has every
  level `m'` with `m ∣ m'`.
* `CongruenceSubgroup.congruenceClasses_eq_iSup`: the congruence classes are the union of the
  characters of positive level.
* `CongruenceSubgroup.mem_congruenceClasses_iff_exists_dvd`: for `N ≠ 0` the level may be taken
  to be a multiple of `N`; for `Γ = Γ(N)` this is the usual definition of `H¹_cong(Γ(N))`.
* `CongruenceSubgroup.mem_congruenceClasses_iff_exists_eq_comp`: congruence classes are exactly
  the pullbacks of characters of the finite congruence quotients.
* `CongruenceSubgroup.comp_inclusion_mem_congruenceClasses`: restriction to a smaller subgroup
  preserves congruence classes.
* `CongruenceSubgroup.H1π_mem_congruenceClassesH1_iff`: the class of a cocycle is a congruence
  class exactly when the cocycle vanishes on some `Γ ∩ Γ(m)`, `m > 0`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, §4.5 (the
  definition of `H¹_cong`) and Lemma 4.6.2.
-/

public section

open scoped MatrixGroups

namespace CongruenceSubgroup

variable (Γ : Subgroup SL(2, ℤ)) (R A : Type*) [Semiring R] [AddCommMonoid A] [Module R A]

/-- The characters of `Γ` with values in `A` that vanish on `Γ ∩ Γ(m)`. For `m = 0` this is
every character, since `Γ(0)` is trivial. -/
def congruenceClassesOfLevel (m : ℕ) : Submodule R (Additive Γ →+ A) where
  carrier := {ψ | ∀ g : Γ, (g : SL(2, ℤ)) ∈ Gamma m → ψ (Additive.ofMul g) = 0}
  add_mem' hψ hφ g hg := by simp [hψ g hg, hφ g hg]
  zero_mem' _ _ := rfl
  smul_mem' c ψ hψ g hg := by simp [hψ g hg]

/-- The **congruence classes**: the characters of `Γ` with values in `A` that vanish on
`Γ ∩ Γ(m)` for some positive level `m`. -/
def congruenceClasses : Submodule R (Additive Γ →+ A) where
  carrier := {ψ | ∃ m, 0 < m ∧ ψ ∈ congruenceClassesOfLevel Γ R A m}
  add_mem' := by
    rintro ψ φ ⟨m, hm, hψ⟩ ⟨n, hn, hφ⟩
    refine ⟨m.lcm n, Nat.lcm_pos hm hn, fun g hg ↦ ?_⟩
    rw [Gamma_lcm_eq_inf] at hg
    simp [hψ g hg.1, hφ g hg.2]
  zero_mem' := ⟨1, one_pos, zero_mem _⟩
  smul_mem' c _ := fun ⟨m, hm, hψ⟩ ↦ ⟨m, hm, Submodule.smul_mem _ c hψ⟩

variable {Γ R A}

@[simp]
theorem mem_congruenceClassesOfLevel {m : ℕ} {ψ : Additive Γ →+ A} :
    ψ ∈ congruenceClassesOfLevel Γ R A m ↔
      ∀ g : Γ, (g : SL(2, ℤ)) ∈ Gamma m → ψ (Additive.ofMul g) = 0 :=
  Iff.rfl

@[simp]
theorem mem_congruenceClasses {ψ : Additive Γ →+ A} :
    ψ ∈ congruenceClasses Γ R A ↔ ∃ m, 0 < m ∧ ψ ∈ congruenceClassesOfLevel Γ R A m :=
  Iff.rfl

/-- A character vanishing on `Γ ∩ Γ(m)` vanishes on the smaller group `Γ ∩ Γ(m')` for every
multiple `m'` of `m`. -/
theorem congruenceClassesOfLevel_le_of_dvd {m m' : ℕ} (h : m ∣ m') :
    congruenceClassesOfLevel Γ R A m ≤ congruenceClassesOfLevel Γ R A m' :=
  fun _ hψ g hg ↦ hψ g (Gamma_le_Gamma_of_dvd h hg)

@[simp]
theorem congruenceClassesOfLevel_zero : congruenceClassesOfLevel Γ R A 0 = ⊤ := by
  refine eq_top_iff.mpr fun ψ _ g hg ↦ ?_
  have : g = 1 := Subtype.ext (by simpa [Gamma_zero_bot] using hg)
  simp [this]

/-- Since `Γ(1)` is all of `SL(2, ℤ)`, the only character of level `1` is zero. -/
@[simp]
theorem congruenceClassesOfLevel_one : congruenceClassesOfLevel Γ R A 1 = ⊥ := by
  refine eq_bot_iff.mpr fun ψ hψ ↦ (Submodule.mem_bot R).mpr ?_
  ext g
  exact hψ g (by simp [Gamma_one_top])

theorem congruenceClassesOfLevel_le_congruenceClasses {m : ℕ} (hm : 0 < m) :
    congruenceClassesOfLevel Γ R A m ≤ congruenceClasses Γ R A :=
  fun _ hψ ↦ ⟨m, hm, hψ⟩

/-- The congruence classes are the union of the characters of the finite congruence quotients,
indexed by the positive levels. The union is directed by
`congruenceClassesOfLevel_le_of_dvd`. -/
theorem congruenceClasses_eq_iSup :
    congruenceClasses Γ R A = ⨆ m : ℕ+, congruenceClassesOfLevel Γ R A m :=
  le_antisymm (fun _ ⟨m, hm, hψ⟩ ↦ Submodule.mem_iSup_of_mem (⟨m, hm⟩ : ℕ+) hψ)
    (iSup_le fun m ↦ congruenceClassesOfLevel_le_congruenceClasses m.pos)

/-- The level of a congruence class may be taken to be a multiple of any given `N ≠ 0`. For
`Γ = Γ(N)` this is the definition of `H¹_cong(Γ(N))` as the characters vanishing on some
`Γ(M)` with `N ∣ M`. -/
theorem mem_congruenceClasses_iff_exists_dvd {N : ℕ} (hN : N ≠ 0) {ψ : Additive Γ →+ A} :
    ψ ∈ congruenceClasses Γ R A ↔
      ∃ M, 0 < M ∧ N ∣ M ∧ ψ ∈ congruenceClassesOfLevel Γ R A M := by
  refine ⟨fun ⟨m, hm, hψ⟩ ↦ ⟨N * m, Nat.mul_pos (Nat.pos_of_ne_zero hN) hm,
    dvd_mul_right N m, congruenceClassesOfLevel_le_of_dvd (dvd_mul_left m N) hψ⟩,
    fun ⟨M, hM, _, hψ⟩ ↦ ⟨M, hM, hψ⟩⟩

/-- Restricting a character of level `m` to a smaller subgroup gives a character of level `m`. -/
theorem comp_inclusion_mem_congruenceClassesOfLevel {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ)
    {m : ℕ} {ψ : Additive Γ →+ A} (hψ : ψ ∈ congruenceClassesOfLevel Γ R A m) :
    ψ.comp (Subgroup.inclusion h).toAdditive ∈ congruenceClassesOfLevel Γ' R A m :=
  fun g hg ↦ hψ (Subgroup.inclusion h g) hg

/-- Restriction to a smaller subgroup preserves congruence classes. -/
theorem comp_inclusion_mem_congruenceClasses {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ)
    {ψ : Additive Γ →+ A} (hψ : ψ ∈ congruenceClasses Γ R A) :
    ψ.comp (Subgroup.inclusion h).toAdditive ∈ congruenceClasses Γ' R A :=
  let ⟨m, hm, hψ⟩ := hψ
  ⟨m, hm, comp_inclusion_mem_congruenceClassesOfLevel h hψ⟩

/-! ### Characters of the finite congruence quotients -/

/-- A character of `Γ` lies in `congruenceClassesOfLevel Γ R A m` exactly when `Γ ∩ Γ(m)` lies in
its kernel. -/
theorem mem_congruenceClassesOfLevel_iff_le_ker {m : ℕ} {ψ : Additive Γ →+ A} :
    ψ ∈ congruenceClassesOfLevel Γ R A m ↔
      (Gamma m).subgroupOf Γ ≤ (AddMonoidHom.toMultiplicativeRight ψ).ker := by
  refine ⟨fun hψ g hg ↦ ?_, fun h g hg ↦ ?_⟩
  · simpa [MonoidHom.mem_ker] using hψ g (Subgroup.mem_subgroupOf.mp hg)
  · simpa [MonoidHom.mem_ker] using h (Subgroup.mem_subgroupOf.mpr hg)

variable (Γ R A) in
/-- **Descent to the congruence quotient.** The characters of `Γ` of level `m` are exactly the
characters of the congruence quotient `Γ ⧸ (Γ ∩ Γ(m))`, each pulled back along the quotient map;
the descended character is unique. The quotient is finite when `m ≠ 0`. -/
noncomputable def congruenceClassesOfLevelEquiv (m : ℕ) :
    (Additive (Γ ⧸ (Gamma m).subgroupOf Γ) →+ A) ≃ₗ[R] congruenceClassesOfLevel Γ R A m where
  toFun φ := ⟨φ.comp (QuotientGroup.mk' _).toAdditive, fun g hg ↦ by
    simp [(QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_subgroupOf.mpr hg)]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ := MonoidHom.toAdditiveLeft (QuotientGroup.lift _
    (AddMonoidHom.toMultiplicativeRight ψ.val)
    (mem_congruenceClassesOfLevel_iff_le_ker.mp ψ.property))
  left_inv φ := by
    ext
    simp [QuotientGroup.lift_mk]
  right_inv ψ := Subtype.ext (AddMonoidHom.ext fun g ↦ by simp [QuotientGroup.lift_mk])

@[simp]
theorem congruenceClassesOfLevelEquiv_apply_apply (m : ℕ)
    (φ : Additive (Γ ⧸ (Gamma m).subgroupOf Γ) →+ A) (g : Γ) :
    (congruenceClassesOfLevelEquiv Γ R A m φ : Additive Γ →+ A) (Additive.ofMul g) =
      φ (Additive.ofMul (g : Γ ⧸ (Gamma m).subgroupOf Γ)) :=
  (rfl)

@[simp]
theorem congruenceClassesOfLevelEquiv_symm_apply_apply (m : ℕ)
    (ψ : congruenceClassesOfLevel Γ R A m) (g : Γ) :
    (congruenceClassesOfLevelEquiv Γ R A m).symm ψ
        (Additive.ofMul (g : Γ ⧸ (Gamma m).subgroupOf Γ)) =
      (ψ : Additive Γ →+ A) (Additive.ofMul g) := by
  simp [congruenceClassesOfLevelEquiv, QuotientGroup.lift_mk]

/-- **Congruence classes are the pullbacks of characters of finite congruence quotients.** -/
theorem mem_congruenceClasses_iff_exists_eq_comp {ψ : Additive Γ →+ A} :
    ψ ∈ congruenceClasses Γ R A ↔
      ∃ m, 0 < m ∧ ∃ φ : Additive (Γ ⧸ (Gamma m).subgroupOf Γ) →+ A,
        ψ = φ.comp (QuotientGroup.mk' _).toAdditive := by
  refine ⟨fun ⟨m, hm, hψ⟩ ↦ ⟨m, hm, (congruenceClassesOfLevelEquiv Γ R A m).symm ⟨ψ, hψ⟩, ?_⟩,
    fun ⟨m, hm, φ, hψ⟩ ↦ ⟨m, hm, hψ ▸ (congruenceClassesOfLevelEquiv Γ R A m φ).property⟩⟩
  exact congrArg Subtype.val ((congruenceClassesOfLevelEquiv Γ R A m).apply_symm_apply ⟨ψ, hψ⟩).symm

/-! ### Congruence classes in `H¹` -/

section H1

open groupCohomology

variable {k : Type} [CommRing k] (A : Rep k Γ) [A.IsTrivial]

variable (Γ) in
/-- The **congruence classes in `H¹(Γ, A)`** for a trivial representation `A`: the classes whose
character, under the isomorphism `H¹(Γ, A) ≅ Hom(Γ, A)` of `groupCohomology.H1IsoOfIsTrivial`,
is a congruence class. For `Γ = Γ(N)` and `A = 𝔽_q` this is `H¹_cong(Γ(N), 𝔽_q)`. -/
noncomputable def congruenceClassesH1 : Submodule k (H1 A) :=
  (congruenceClasses Γ k A).comap (H1IsoOfIsTrivial A).toLinearEquiv.toLinearMap

@[simp]
theorem mem_congruenceClassesH1 {x : H1 A} :
    x ∈ congruenceClassesH1 Γ A ↔ (H1IsoOfIsTrivial A).hom x ∈ congruenceClasses Γ k A := by
  simp [congruenceClassesH1]

/-- The class of a cocycle `f` is a congruence class exactly when `f` vanishes on `Γ ∩ Γ(m)` for
some positive level `m`. -/
theorem H1π_mem_congruenceClassesH1_iff (f : cocycles₁ A) :
    H1π A f ∈ congruenceClassesH1 Γ A ↔
      ∃ m, 0 < m ∧ ∀ g : Γ, (g : SL(2, ℤ)) ∈ Gamma m → f g = 0 := by
  simp

variable (Γ) in
/-- The isomorphism `H¹(Γ, A) ≅ Hom(Γ, A)` restricts to an isomorphism between the congruence
classes in `H¹(Γ, A)` and the congruence classes of characters. -/
noncomputable def congruenceClassesH1Equiv :
    congruenceClassesH1 Γ A ≃ₗ[k] congruenceClasses Γ k A :=
  (H1IsoOfIsTrivial A).toLinearEquiv.ofSubmodules _ _
    (Submodule.map_comap_eq_of_surjective (H1IsoOfIsTrivial A).toLinearEquiv.surjective _)

@[simp]
theorem coe_congruenceClassesH1Equiv_apply (x : congruenceClassesH1 Γ A) :
    (congruenceClassesH1Equiv Γ A x : Additive Γ →+ A) = (H1IsoOfIsTrivial A).hom x :=
  (rfl)

end H1

end CongruenceSubgroup
