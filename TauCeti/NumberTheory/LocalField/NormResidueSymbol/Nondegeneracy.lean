/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Degree
public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Steinberg
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.LinearAlgebra.LinearIndependent.MonoidHom

/-!
# The norm criterion and nondegeneracy of the norm-residue symbol

Let `K` be a nonarchimedean local field containing the `n`-th roots of unity (`n ≠ 0`). This file
relates the degree-`n` norm-residue symbol `(a, b)_{K, n}` to norm groups of radical and Kummer
extensions of `K` and establishes that the induced pairing on `Kˣ ⧸ (Kˣ)ⁿ` is perfect:

* **The norm criterion in both arguments**
  (`TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_left`,
  `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_right`): `(a, b)_{K, n} = 1` if and only if
  `a` is a norm from `K(ⁿ√b)`, and if and only if `b` is a norm from `K(ⁿ√a)`.
* **Nondegeneracy and the perfect pairing** (`TauCeti.forall_normResidueSymbol_eq_one_left_iff`,
  `TauCeti.forall_normResidueSymbol_eq_one_right_iff`, `TauCeti.normResidueSymbolPairingEquiv`): an
  element of `Kˣ` pairs trivially with all of `Kˣ` on either side if and only if it is an `n`-th
  power, and `TauCeti.normResidueSymbolPairing` is a multiplicative isomorphism
  `Kˣ ⧸ (Kˣ)ⁿ ≃* (Kˣ ⧸ (Kˣ)ⁿ →* μ_n(K))`.
* **Orthogonal subgroups and norm groups of Kummer extensions** (`TauCeti.normResidueOrthogonal`,
  `TauCeti.normGroup_kummerField_eq_normResidueOrthogonal`,
  `TauCeti.normResidueOrthogonal_normResidueOrthogonal`,
  `TauCeti.normGroup_kummerField_normResidueOrthogonal`): for any subgroup `B ≤ Kˣ`, the norm group
  of `K(B^{1/n})` is the orthogonal subgroup `B^⊥`, of index `[B : B ∩ (Kˣ)ⁿ]`; when
  `(Kˣ)ⁿ ≤ A ≤ Kˣ`, `(A^⊥)^⊥ = A` and `A` is the norm group of `K((A^⊥)^{1/n})`.

## Main definitions

* `TauCeti.normResidueSymbolPairingEquiv`: the perfect-pairing isomorphism
  `powerClassQuotient Kˣ n ≃* (powerClassQuotient Kˣ n →* rootsOfUnity n K)`.
* `TauCeti.normResidueOrthogonal`: the orthogonal subgroup `A^⊥ ≤ Kˣ` under the degree-`n`
  norm-residue symbol.

## Main results

* `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_left`,
  `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_left`: `(a, b)_{K, n} = 1` iff
  `a ∈ N_{K(ⁿ√b)/K}(K(ⁿ√b)ˣ)`.
* `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_right`,
  `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_right`: `(a, b)_{K, n} = 1` iff
  `b ∈ N_{K(ⁿ√a)/K}(K(ⁿ√a)ˣ)`.
* `TauCeti.forall_normResidueSymbol_eq_one_left_iff`,
  `TauCeti.forall_normResidueSymbol_eq_one_right_iff`: `(a, b)_{K, n} = 1` for all `a` (resp. all
  `b`) iff `b ∈ (Kˣ)ⁿ` (resp. `a ∈ (Kˣ)ⁿ`).
* `TauCeti.normResidueSymbolPairing_bijective`, `TauCeti.normResidueSymbolPairing_flip_bijective`:
  both adjoints of `normResidueSymbolPairing` are bijective.
* `TauCeti.normGroup_kummerField_eq_normResidueOrthogonal`: `N_{K(B^{1/n})/K}(K(B^{1/n})ˣ) = B^⊥`.
* `TauCeti.index_normResidueOrthogonal`: `[Kˣ : B^⊥] = [B : B ∩ (Kˣ)ⁿ]`.
* `TauCeti.normResidueOrthogonal_normResidueOrthogonal`: `(A^⊥)^⊥ = A` whenever `(Kˣ)ⁿ ≤ A`.
* `TauCeti.normGroup_kummerField_normResidueOrthogonal`: `N_{K((A^⊥)^{1/n})/K} = A` whenever
  `(Kˣ)ⁿ ≤ A`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, Chapter IV, §5,
  (5.1) Proposition (5)–(6), Corollary, and (5.2) Theorem, pp. 143–145.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Theorem 4.4 (c)–(d), p. 113.
-/

public section

noncomputable section

open IntermediateField

namespace TauCeti

open ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-! ### The norm criterion in both arguments -/

/-- **The norm criterion in the Artin argument.** If `L = K(s)` with `s ^ n = b`, then
`(a, b)_{K, n} = 1` if and only if `a` lies in the norm group `N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_left {L : Type*} [Field L] [Algebra K L]
    [Module.Finite K L] {a b : Kˣ} {s : L} (hs : s ^ n = algebraMap K L b) (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ a ∈ normGroup K L := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K a)
  set τ : Gal(L/K) := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ)
  -- Restricting a representative `σ` of `Art_K(a)` to `L` moves `s` by `(a, b)_{K, n}`.
  have hτ_apply : τ s = algebraMap K L ((normResidueSymbol K n a b : Kˣ) : K) * s := by
    apply ι.injective
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, ι.commutes,
      ι.restrictNormalHom_commutes]
    exact normResidueSymbol_spec_separableClosure a b σ hσ (β := ι s)
      (by rw [← map_pow, hs, ι.commutes])
  have hs0 : s ≠ 0 := ne_zero_of_pow_eq_algebraMap hs
  have hsym : normResidueSymbol K n a b = 1 ↔ τ = 1 := by
    refine ⟨fun h1 ↦ TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top hgen ?_,
      fun h1 ↦ ?_⟩
    · rintro _ (rfl : _ = s)
      simpa [h1] using hτ_apply
    · rw [h1, AlgEquiv.one_apply] at hτ_apply
      have hval : algebraMap K L ((normResidueSymbol K n a b : Kˣ) : K) = 1 :=
        mul_right_cancel₀ hs0 (by simpa using hτ_apply.symm)
      exact Subtype.ext (Units.ext ((algebraMap K L).injective (by simpa using hval)))
  rw [hsym, ← localArtinMap_eq_zero_iff K L ι a, artinMap_restrict K L ι a σ hσ, ofMul_eq_zero,
    ← map_one Group.Abelianization.of, Group.Abelianization.of_injective.eq_iff]

/-- **The norm criterion for a simple radical subfield, Artin argument.** For an `n`-th root `β` of
`b` in an extension `E / K` with `K⟮β⟯` finite over `K` (automatic when `E / K` is algebraic),
`(a, b)_{K, n} = 1` if and only if `a ∈ N_{K⟮β⟯/K}(K⟮β⟯ˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_left {E : Type*} [Field E] [Algebra K E]
    {a b : Kˣ} {β : E} [Module.Finite K K⟮β⟯] (hβ : β ^ n = algebraMap K E b) :
    normResidueSymbol K n a b = 1 ↔ a ∈ normGroup K K⟮β⟯ :=
  normResidueSymbol_eq_one_iff_mem_normGroup_left (s := AdjoinSimple.gen K β)
    (Subtype.ext (by simpa using hβ)) (adjoin_adjoinSimple_gen_eq_top β)

/-- **The norm criterion in the radical argument.** If `L = K(s)` with `s ^ n = a`, then
`(a, b)_{K, n} = 1` if and only if `b` lies in the norm group `N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_right {L : Type*} [Field L] [Algebra K L]
    [Module.Finite K L] {a b : Kˣ} {s : L} (hs : s ^ n = algebraMap K L a) (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ b ∈ normGroup K L := by
  rw [normResidueSymbol_swap, inv_eq_one, normResidueSymbol_eq_one_iff_mem_normGroup_left hs hgen]

/-- **The norm criterion for a simple radical subfield, radical argument.** For an `n`-th root `α`
of `a` in an extension `E / K` with `K⟮α⟯` finite over `K` (automatic when `E / K` is algebraic),
`(a, b)_{K, n} = 1` if and only if `b ∈ N_{K⟮α⟯/K}(K⟮α⟯ˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_right {E : Type*} [Field E] [Algebra K E]
    {a b : Kˣ} {α : E} [Module.Finite K K⟮α⟯] (hα : α ^ n = algebraMap K E a) :
    normResidueSymbol K n a b = 1 ↔ b ∈ normGroup K K⟮α⟯ := by
  rw [normResidueSymbol_swap, inv_eq_one,
    normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_left hα]

/-! ### Nondegeneracy and the perfect pairing on power classes -/

/-- **Nondegeneracy in the radical argument.** A unit `b ∈ Kˣ` pairs trivially with every Artin
argument `a ∈ Kˣ` if and only if `b` is an `n`-th power in `Kˣ`. -/
theorem forall_normResidueSymbol_eq_one_left_iff {b : Kˣ} :
    (∀ a : Kˣ, normResidueSymbol K n a b = 1) ↔ b ∈ powerSubgroup Kˣ n := by
  refine ⟨fun h ↦ ?_, fun hb a ↦ ?_⟩
  · obtain ⟨β, hβ⟩ :=
      IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b) (NeZero.pos n)
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
    have hgen_pow : (AdjoinSimple.gen K β) ^ n = algebraMap K K⟮β⟯ b :=
      Subtype.ext (by simpa using hβ)
    have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hgen_pow (adjoin_adjoinSimple_gen_eq_top β)
    have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hgen_pow (adjoin_adjoinSimple_gen_eq_top β)
    have htop : normGroup K K⟮β⟯ = ⊤ :=
      eq_top_iff.2 fun a _ ↦ (normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_left hβ).1 (h a)
    have hdeg : Module.finrank K K⟮β⟯ = 1 := by
      rw [← index_normGroup_of_isMulCommutative K K⟮β⟯, htop, Subgroup.index_top]
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.1 hdeg)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact ne_zero_of_pow_eq_algebraMap hβ (by rw [← hc, map_zero])
    exact (mem_powerSubgroup_iff n).2 ⟨Units.mk0 c hc0,
      Units.ext ((algebraMap K (AlgebraicClosure K)).injective (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hc, hβ]))⟩
  · obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 hb
    exact normResidueSymbol_pow_right_eq_one a c

/-- **Nondegeneracy in the Artin argument.** A unit `a ∈ Kˣ` pairs trivially with every radical
argument `b ∈ Kˣ` if and only if `a` is an `n`-th power in `Kˣ`. -/
theorem forall_normResidueSymbol_eq_one_right_iff {a : Kˣ} :
    (∀ b : Kˣ, normResidueSymbol K n a b = 1) ↔ a ∈ powerSubgroup Kˣ n := by
  simp_rw [normResidueSymbol_swap (n := n) _ a, inv_eq_one]
  exact forall_normResidueSymbol_eq_one_left_iff

/-- The left adjoint of the norm-residue pairing on `Kˣ ⧸ (Kˣ)ⁿ` is injective. -/
theorem normResidueSymbolPairing_injective :
    Function.Injective (normResidueSymbolPairing (K := K) (n := n)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot, powerClassHom_apply, QuotientGroup.eq_one_iff,
    ← forall_normResidueSymbol_eq_one_right_iff (K := K) (n := n)]
  intro b
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk, MonoidHom.one_apply] using
    DFunLike.congr_fun hx (QuotientGroup.mk b)

/-- **The norm-residue symbol induces a perfect pairing on `Kˣ ⧸ (Kˣ)ⁿ`** (left adjoint). -/
theorem normResidueSymbolPairing_bijective :
    Function.Bijective (normResidueSymbolPairing (K := K) (n := n)) :=
  bijective_of_injective_to_monoidHom
    (ι := (Units.coeHom K).comp (rootsOfUnity n K).subtype)
    (Units.val_injective.comp Subtype.val_injective)
    normResidueSymbolPairing_injective

/-- **The norm-residue symbol induces a perfect pairing on `Kˣ ⧸ (Kˣ)ⁿ`** (right adjoint). -/
theorem normResidueSymbolPairing_flip_bijective :
    Function.Bijective (normResidueSymbolPairing (K := K) (n := n)).flip := by
  have hflip : ⇑(normResidueSymbolPairing (K := K) (n := n)).flip =
      Inv.inv ∘ ⇑(normResidueSymbolPairing (K := K) (n := n)) :=
    funext fun y ↦ MonoidHom.ext fun x ↦ normResidueSymbolPairing_swap y x
  rw [hflip]
  exact inv_involutive.bijective.comp normResidueSymbolPairing_bijective

/-- The right adjoint of the norm-residue pairing on `Kˣ ⧸ (Kˣ)ⁿ` is injective. -/
theorem normResidueSymbolPairing_flip_injective :
    Function.Injective (normResidueSymbolPairing (K := K) (n := n)).flip :=
  normResidueSymbolPairing_flip_bijective.injective

variable (K n) in
/-- **The perfect norm-residue pairing isomorphism**
`Kˣ ⧸ (Kˣ)ⁿ ≃* (Kˣ ⧸ (Kˣ)ⁿ →* μ_n(K))` induced by `normResidueSymbolPairing`. -/
def normResidueSymbolPairingEquiv :
    powerClassQuotient Kˣ n ≃* (powerClassQuotient Kˣ n →* rootsOfUnity n K) :=
  MulEquiv.ofBijective normResidueSymbolPairing normResidueSymbolPairing_bijective

/-- Applying `normResidueSymbolPairingEquiv` computes `normResidueSymbolPairing`. -/
@[simp]
theorem normResidueSymbolPairingEquiv_apply (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairingEquiv K n x = normResidueSymbolPairing x :=
  (rfl)

/-! ### Orthogonal subgroups and norm groups of Kummer extensions -/

variable (K n) in
/-- The **orthogonal subgroup** `A^⊥` of a subgroup `A ≤ Kˣ` under the degree-`n` norm-residue
symbol: the subgroup of `a ∈ Kˣ` pairing trivially with every `b ∈ A`. By skew symmetry, this is
equivalently `{a ∈ Kˣ | ∀ b ∈ A, (b, a)_{K, n} = 1}` (`mem_normResidueOrthogonal_iff_right`). -/
def normResidueOrthogonal (A : Subgroup Kˣ) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∀ b ∈ A, normResidueSymbol K n a b = 1}
  one_mem' _ _ := normResidueSymbol_one_left _
  mul_mem' {a₁ a₂} ha₁ ha₂ b hb := by
    rw [normResidueSymbol_mul_left, ha₁ b hb, ha₂ b hb, mul_one]
  inv_mem' {a} ha b hb := by
    rw [normResidueSymbol_inv_left, ha b hb, inv_one]

/-- A unit `a` lies in `A^⊥` if and only if `(a, b)_{K, n} = 1` for every `b ∈ A`. -/
@[simp]
theorem mem_normResidueOrthogonal_iff {A : Subgroup Kˣ} {a : Kˣ} :
    a ∈ normResidueOrthogonal K n A ↔ ∀ b ∈ A, normResidueSymbol K n a b = 1 :=
  (Iff.rfl)

/-- By skew symmetry, `a` lies in `A^⊥` if and only if `(b, a)_{K, n} = 1` for every `b ∈ A`. -/
theorem mem_normResidueOrthogonal_iff_right {A : Subgroup Kˣ} {a : Kˣ} :
    a ∈ normResidueOrthogonal K n A ↔ ∀ b ∈ A, normResidueSymbol K n b a = 1 := by
  simp_rw [mem_normResidueOrthogonal_iff, normResidueSymbol_swap (n := n) _ a, inv_eq_one]

/-- Every orthogonal subgroup contains the `n`-th power subgroup `(Kˣ)ⁿ`. -/
theorem powerSubgroup_le_normResidueOrthogonal (A : Subgroup Kˣ) :
    powerSubgroup Kˣ n ≤ normResidueOrthogonal K n A := by
  intro x hx b _
  obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 hx
  exact normResidueSymbol_pow_left_eq_one c b

/-- Every orthogonal subgroup `A^⊥` has finite index in `Kˣ`. -/
instance instFiniteIndexNormResidueOrthogonal (A : Subgroup Kˣ) :
    (normResidueOrthogonal K n A).FiniteIndex :=
  Subgroup.finiteIndex_of_le (powerSubgroup_le_normResidueOrthogonal A)

/-- Orthogonality is symmetric as a relation between subgroups: `A ≤ B^⊥ ↔ B ≤ A^⊥`. -/
theorem le_normResidueOrthogonal_iff {A B : Subgroup Kˣ} :
    A ≤ normResidueOrthogonal K n B ↔ B ≤ normResidueOrthogonal K n A :=
  ⟨fun h _ hb _ ha ↦ (mem_normResidueOrthogonal_iff_right.1 (h ha)) _ hb,
    fun h _ ha _ hb ↦ (mem_normResidueOrthogonal_iff_right.1 (h hb)) _ ha⟩

/-- Every subgroup is contained in its double orthogonal. -/
theorem le_normResidueOrthogonal_normResidueOrthogonal (A : Subgroup Kˣ) :
    A ≤ normResidueOrthogonal K n (normResidueOrthogonal K n A) :=
  le_normResidueOrthogonal_iff.1 le_rfl

/-- Taking the orthogonal subgroup reverses inclusions. -/
theorem normResidueOrthogonal_antitone : Antitone (normResidueOrthogonal K n) :=
  fun _ _ h ↦ le_normResidueOrthogonal_iff.2
    (h.trans (le_normResidueOrthogonal_normResidueOrthogonal _))

/-- The orthogonal of the trivial subgroup is all of `Kˣ`. -/
@[simp]
theorem normResidueOrthogonal_bot : normResidueOrthogonal K n ⊥ = ⊤ := by
  ext a
  simp

/-- The orthogonal of `Kˣ` is the `n`-th power subgroup `(Kˣ)ⁿ`. -/
@[simp]
theorem normResidueOrthogonal_top : normResidueOrthogonal K n ⊤ = powerSubgroup Kˣ n := by
  ext a
  simpa using forall_normResidueSymbol_eq_one_right_iff (K := K) (n := n) (a := a)

/-- The orthogonal of `(Kˣ)ⁿ` is all of `Kˣ`. -/
@[simp]
theorem normResidueOrthogonal_powerSubgroup :
    normResidueOrthogonal K n (powerSubgroup Kˣ n) = ⊤ :=
  eq_top_iff.2 (le_normResidueOrthogonal_iff.2 (powerSubgroup_le_normResidueOrthogonal ⊤))

/-- The orthogonal of a join of two subgroups is the meet of their orthogonals. -/
@[simp]
theorem normResidueOrthogonal_sup (A B : Subgroup Kˣ) :
    normResidueOrthogonal K n (A ⊔ B) =
      normResidueOrthogonal K n A ⊓ normResidueOrthogonal K n B := by
  refine le_antisymm
    (le_inf (normResidueOrthogonal_antitone le_sup_left)
      (normResidueOrthogonal_antitone le_sup_right)) ?_
  rw [le_normResidueOrthogonal_iff, sup_le_iff]
  exact ⟨le_normResidueOrthogonal_iff.2 inf_le_left, le_normResidueOrthogonal_iff.2 inf_le_right⟩

/-- **The norm group of a Kummer extension is the orthogonal subgroup.** Whenever every element of
`B ≤ Kˣ` has an `n`-th root in `E`, `N_{K(B^{1/n})/K}(K(B^{1/n})ˣ) = B^⊥`. -/
theorem normGroup_kummerField_eq_normResidueOrthogonal {E : Type*} [Field E] [Algebra K E]
    {B : Subgroup Kˣ} (hroots : ∀ b ∈ B, ∃ x : E, x ^ n = algebraMap K E b) :
    normGroup K (kummerField E n B) = normResidueOrthogonal K n B := by
  set M := kummerField E n B
  refine le_antisymm (fun a ha ↦ mem_normResidueOrthogonal_iff.2 fun b hb ↦ ?_) (fun a ha ↦ ?_)
  · obtain ⟨y, hy⟩ := exists_pow_eq_kummerField hroots b hb
    exact (normResidueSymbol_eq_one_iff_mem_normGroup_adjoin_left hy).2
      (K⟮y⟯.val.normGroup_le_normGroup ha)
  · let ι : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K a)
    rw [← localArtinMap_eq_zero_iff K M ι a, artinMap_restrict K M ι a σ hσ, ofMul_eq_zero,
      ← map_one Group.Abelianization.of, Group.Abelianization.of_injective.eq_iff]
    refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top
      adjoin_pow_eq_algebraMap_kummerField_eq_top ?_
    rintro y ⟨b, hb, hy⟩
    apply ι.injective
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ι.restrictNormalHom_commutes,
      normResidueSymbol_spec_separableClosure a b σ hσ (β := ι y)
        (by rw [← map_pow, hy, ι.commutes]),
      mem_normResidueOrthogonal_iff.1 ha b hb, Subgroup.coe_one, Units.val_one, map_one, one_mul]

/-- The index of `B^⊥` in `Kˣ` equals the relative index `[B : B ∩ (Kˣ)ⁿ]`. -/
theorem index_normResidueOrthogonal (B : Subgroup Kˣ) :
    (normResidueOrthogonal K n B).index = (powerSubgroup Kˣ n).relIndex B := by
  have hroots : ∀ b ∈ B, ∃ x : AlgebraicClosure K,
      x ^ n = algebraMap K (AlgebraicClosure K) b :=
    fun b _ ↦ IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b) (NeZero.pos n)
  rw [← normGroup_kummerField_eq_normResidueOrthogonal hroots,
    index_normGroup_of_isMulCommutative, finrank_kummerField hroots,
    powerSubgroup_eq_range_powMonoidHom]

/-- In a separably closed extension `E` of `K` (such as `SeparableClosure K` or
`AlgebraicClosure K`), the norm group of `K(B^{1/n})` is `B^⊥`. -/
theorem normGroup_kummerField_eq_normResidueOrthogonal_of_isSepClosed (E : Type*) [Field E]
    [Algebra K E] [IsSepClosed E] (B : Subgroup Kˣ) :
    normGroup K (kummerField E n B) = normResidueOrthogonal K n B := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have := hζ.neZero'
  have : NeZero (n : E) := .nat_of_injective (algebraMap K E).injective
  exact normGroup_kummerField_eq_normResidueOrthogonal fun b _ ↦
    IsSepClosed.exists_pow_nat_eq (algebraMap K E b) n

/-- **Double-orthogonal theorem for subgroups containing `(Kˣ)ⁿ`.** If `(Kˣ)ⁿ ≤ A ≤ Kˣ`, then
`(A^⊥)^⊥ = A`. -/
theorem normResidueOrthogonal_normResidueOrthogonal {A : Subgroup Kˣ}
    (hA : powerSubgroup Kˣ n ≤ A) :
    normResidueOrthogonal K n (normResidueOrthogonal K n A) = A := by
  have : (powerSubgroup Kˣ n).IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
  have : A.FiniteIndex := Subgroup.finiteIndex_of_le hA
  have hmul₁ := Subgroup.relIndex_mul_index hA
  have hmul₂ :=
    Subgroup.relIndex_mul_index (powerSubgroup_le_normResidueOrthogonal (K := K) (n := n) A)
  rw [← index_normResidueOrthogonal (normResidueOrthogonal K n A),
    index_normResidueOrthogonal A, ← hmul₁, mul_comm _ A.index] at hmul₂
  have hidx : (normResidueOrthogonal K n (normResidueOrthogonal K n A)).index = A.index :=
    Nat.eq_of_mul_eq_mul_right Subgroup.relIndex_pos hmul₂
  exact (Subgroup.eq_of_index_dvd_index (le_normResidueOrthogonal_normResidueOrthogonal A)
    (by rw [hidx])).symm

/-- **Norm groups of Kummer extensions via orthogonals** (Fesenko–Vostokov, Chapter IV, §5,
Theorem (5.2)). If `(Kˣ)ⁿ ≤ A ≤ Kˣ` and every element of `A^⊥` has an `n`-th root in `E`, then
`A` is the norm group of the Kummer extension `K((A^⊥)^{1/n})`. -/
theorem normGroup_kummerField_normResidueOrthogonal {E : Type*} [Field E] [Algebra K E]
    {A : Subgroup Kˣ} (hA : powerSubgroup Kˣ n ≤ A)
    (hroots : ∀ b ∈ normResidueOrthogonal K n A, ∃ x : E, x ^ n = algebraMap K E b) :
    normGroup K (kummerField E n (normResidueOrthogonal K n A)) = A := by
  rw [normGroup_kummerField_eq_normResidueOrthogonal hroots,
    normResidueOrthogonal_normResidueOrthogonal hA]

/-- In a separably closed extension `E` of `K`, every subgroup `A ≤ Kˣ` containing `(Kˣ)ⁿ` is the
norm group of `K((A^⊥)^{1/n})`. -/
theorem normGroup_kummerField_normResidueOrthogonal_of_isSepClosed (E : Type*) [Field E]
    [Algebra K E] [IsSepClosed E] {A : Subgroup Kˣ} (hA : powerSubgroup Kˣ n ≤ A) :
    normGroup K (kummerField E n (normResidueOrthogonal K n A)) = A := by
  rw [normGroup_kummerField_eq_normResidueOrthogonal_of_isSepClosed,
    normResidueOrthogonal_normResidueOrthogonal hA]

end TauCeti
